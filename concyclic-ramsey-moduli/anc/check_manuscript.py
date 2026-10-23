"""Verify the literal LaTeX certificates against the exact receipts in checks/."""
from pathlib import Path
from fractions import Fraction as Q
import json
import re
import sympy as sp
from sympy.parsing.sympy_parser import (
    parse_expr, standard_transformations, convert_xor,
    implicit_multiplication_application,
)


def main():
    anc = Path(__file__).resolve().parent
    root = anc.parent
    paper = root / "source"
    jet = json.loads((anc / "checks/second_jet_certificate.json").read_text())
    ellipse = json.loads((anc / "checks/elliptic.json").read_text())
    example = (paper / "sections/06-appendix-example.tex").read_text()
    elliptic = (paper / "sections/07-elliptic.tex").read_text()
    identities = (paper / "sections/08-certificates.tex").read_text()

    block = re.search(r"\\begin\{pmatrix\}\s*(-28&.*?)\\end\{pmatrix\}", example, re.S).group(1)
    matrix = [[int(x.strip()) for x in row.strip().split("&")]
              for row in block.strip().split(r"\\")]
    assert matrix == jet["integer_minor"]
    assert str(jet["integer_determinant"]) in example
    assert "30611001600000" in example

    rows = re.findall(r"^([0-7])&\$\\dfrac\{([0-9]+)\}\{([0-9]+)\}\$", elliptic, re.M)
    assert [int(i) for i, _, _ in rows] == list(range(8))
    assert [Q(int(a), int(b)) for _, a, b in rows] == [Q(p[0]) for p in ellipse["test_points"]]
    assert ellipse["lexicographic_difference_signs"] in elliptic

    syms = dict(zip("xuyv", sp.symbols("x u y v")))
    transformations = standard_transformations + (convert_xor, implicit_multiplication_application)
    for name, key in [("Q_1", "pair_identity_quotient_y"),
                      ("Q_2", "pair_identity_quotient_v")]:
        literal = re.search(name + r"=(-20.*?)(?=\\end\{align\*\})", identities, re.S).group(1)
        for token in (r"\bigl", r"\bigr", r"\\", "&"):
            literal = literal.replace(token, "")
        literal = literal.strip().rstrip(",. ")
        assert re.fullmatch(r"[0-9xuyv+\-*^()\s,.]*", literal)
        actual = parse_expr(literal, local_dict=syms, transformations=transformations)
        expected = sp.sympify(ellipse[key], locals=syms)
        assert sp.expand(actual - expected) == 0

    tex = "\n".join(p.read_text() for p in paper.rglob("*.tex"))
    labels = re.findall(r"\\label\{([^}]+)\}", tex)
    assert len(labels) == len(set(labels)), "Duplicate labels"
    refs = re.findall(r"\\(?:eqref|ref)\{([^}]+)\}", tex)
    assert set(refs) <= set(labels), sorted(set(refs) - set(labels))
    bib = (paper / "references.bib").read_text()
    bibkeys = set(re.findall(r"@\w+\{([^,]+),", bib))
    cited = set()
    for match in re.finditer(r"\\cite(?:\[[^]]*\])?\{([^}]+)\}", tex):
        cited.update(match.group(1).split(","))
    assert cited == bibkeys, (cited - bibkeys, bibkeys - cited)

    report = {
        "literal_ten_by_ten_matrix": True,
        "literal_eight_orbit_values": True,
        "literal_35_difference_signs": True,
        "literal_polynomial_quotients": True,
        "all_labels_unique_and_all_references_resolve_in_source": True,
        "bibliography_exactly_matches_citations": True,
        "status": "PASS",
    }
    (anc / "manuscript-check.json").write_text(json.dumps(report, indent=2) + "\n")
    print("PASS: literal matrix, eight fractions, 35 signs, and both polynomial quotients.")
    print("PASS: unique labels, references, and six bibliography entries.")


if __name__ == "__main__":
    main()
