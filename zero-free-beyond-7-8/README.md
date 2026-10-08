# A zero-free half-plane beyond seven eighths for Dirichlet L-functions and finite-order Hecke L-functions over Q(sqrt(-3))

Jizhou Guo — Dots Studio, Rednote  
mitsuha2021b@gmail.com

Taking the written statements of OpenAI's September 30, 2026 paper as input, the paper proves that every Dirichlet L-function (all moduli), every finite-order Hecke L-function over Q(sqrt(-3)), and the Riemann zeta function have no zeros with Re(s) > sigma_dagger. Here sigma_dagger is the unique root in (0.8749570194, 0.8749570195) of

    7884 s^3 - 18819 s^2 + 14643 s - 3686.

In particular, Re(s) > 43747851/50000000 = 7/8 - 2149/50000000 is zero-free. Principal poles at s=1 are allowed. Optimising the skew parameter gives the quadratic endpoint (1507 - 2 sqrt(921))/1653; extending the plain fourth-moment range from [3/4, 1] to [37/50, 1] gives the cubic endpoint. Hypothesis 11.1 is a single unproved mean-square estimate for H >= D^(99/100); its conditional consequence Re(s) > 328/375 is stated separately.

The analytic construction and the unchanged arithmetic inputs are due to OpenAI. References to the OpenAI manuscripts use repository [openai/math](https://github.com/openai/math) at commit adc7f1241b42e322a6451854ab7e4b4c146bf78a:

- [The Quasi-Riemann Hypothesis: A Zero-Free Half-Plane Re(s) > 7/8](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-Quasi-Riemann-Hypothesis-September-30-2026/paper.pdf), September 30, 2026. PDF SHA-256: 8fe93046f8cf5ef1ba5969c89addc02d76311adc4ee907509ff9cd96f7ec99e7.
- [The Quasi-Riemann Hypothesis](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-Quasi-Riemann-Hypothesis-October-5-2026/paper2.pdf), October 5, 2026, used for the family in the conditional mean-square hypothesis. PDF SHA-256: f919b57829b178c8e60e7c17b018cf773e7907cf642ef5a3347d8a826e8dbf18.
- [Lean scope document, lean/docs/003.md](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/docs/003.md). It describes formalizations of the 7/8 bounds for zeta, all Dirichlet L-functions and finite-order Hecke L-functions over Q(sqrt(-3)), with principal poles excluded. The present paper uses the intermediate statements of the September 30 paper as written, with their hypotheses recorded in the appendices.

Z. Gao independently obtained the boundary 20999/24000 with the same parameters ell=1001/6000 and b=1/8 in [A quantitative refinement of the seven-eighths zero-free half-plane](https://github.com/Gaozhongpai/seven-eighths-refinement-certificates/blob/309a757ea539e2bf11558d8b5539e1269b792386/report.pdf), a draft dated October 7, 2026. The cited repository version is commit 309a757ea539e2bf11558d8b5539e1269b792386. Gao's fixed-skew envelope has the limiting boundary approximately 0.8749572006. The present paper adds the optimisation of the skew and the extension of the plain fourth-moment range described above.

A model computation in [tomoto0/quasi-riemann-hypothesis-7-8-verification](https://github.com/tomoto0/quasi-riemann-hypothesis-7-8-verification/tree/b83a73c6cb626a391e551baafdb7d0cceafaa55a), dated October 7, 2026, applies the exponent formulas of the OpenAI paper outside their stated ranges and indicates a boundary near 0.87496 from a change of geometry alone.

Read [paper.pdf](paper.pdf). The complete LaTeX source is in source/. With Tectonic installed, compile from that directory:

    cd source
    tectonic main.tex

Alternatively, the included bibliography permits compilation with pdfLaTeX:

    pdflatex main.tex
    pdflatex main.tex

To regenerate the bibliography after changing references.bib, run bibtex main between the two pdfLaTeX passes.

From this directory, rerun the exact-arithmetic certificates with Python 3.9 or later:

    python3 anc/run_all.py

Only the standard library is required. The runner executes the scripts serially in one process and writes their outputs in anc/. The scripts verify algebra and rational intervals; the analytic proofs are in the paper. SHA256SUMS records the distributed files.
