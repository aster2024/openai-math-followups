# First Neumann eigenfunctions of convex planar domains attain their extrema on the boundary

Jizhou Guo — mitsuha2021b@gmail.com — 10 October 2026

[**Paper (PDF, 32 pages)**](paper.pdf) · [LaTeX source](source/)

## Results

Let D be a non-empty bounded open convex subset of the plane, with no smoothness assumption on its boundary
(polygons are included). Let μ be its first positive Neumann eigenvalue and u any non-zero real eigenfunction
for μ, taken as its continuous representative on the closure of D.

**Theorem 1.1.** The maximum of u over the closure of D equals its maximum over ∂D, and likewise for the
minimum. This holds both when μ is simple and when it is double, for every member of the eigenspace.

**Theorem 1.2.** u has no strict local extremum and no isolated local extremum in D. Every isolated critical
point of u in D has index zero. At every critical point in D the Hessian has rank one. No compact closed curve
of critical points is contained in D.

**Theorem 1.3.** The multiplicity of μ is at most two. The nodal set of u in D is a single analytic arc without
critical points of u on it, whose two ends converge to two distinct boundary points; the boundary trace of u has
exactly these two zeros and changes sign at each.

Theorem 1.1 is the weak form of the hot spots property (HS2 in the notation of Bañuelos and Burdzy): it does not
assert that every extreme point lies on the boundary, nor that the gradient of u is non-zero in D. Theorem 1.2
lists what the limiting argument retains.

## What the proofs use

Theorems 1.1 and 1.2 are deduced from Theorem 1.1 of OpenAI's paper
[Strict hot spots and absence of interior critical points on smooth simply connected planar domains](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Strict-hot-spots-and-absence-of-interior-critical-points-on-smooth-simply-connected-planar-domains-September-24-2026/main.pdf)
(24 September 2026; family 369 of the [OpenAI mathematics release](https://github.com/openai/math), pinned to
commit `adc7f1241b42e322a6451854ab7e4b4c146bf78a`): on every bounded simply connected planar domain with C^∞
boundary, every non-zero eigenfunction for the first positive Neumann eigenvalue has non-vanishing gradient in
the interior, and its interior values lie strictly between its boundary extremes.

- Only the statement of that theorem is used. For a simple eigenvalue it is applied to smooth strictly convex
  approximations of D, and Theorem 1.1 is then an approximation corollary; the extension, H² and spectral
  convergence estimates follow the classical route (in particular Bérard–Helffer 2021, Section 2).
- For a double eigenvalue, a fixed approximating sequence need not reach every member of the eigenspace (rounded
  rectangles tending to a square reach one direction). The paper proves that the first-order shape perturbation
  of the eigenvalue maps onto the traceless symmetric 2 × 2 matrices for every convex D, selects a prescribed
  member by a quantitative perturbation, and applies the OpenAI theorem to smooth images of the approximating
  domains under diffeomorphisms close to the identity. These images need not be convex.
- Theorem 1.3 does not use the OpenAI theorem. For simply connected domains with smooth boundary the
  multiplicity bound is due to Nadirashvili (1987); the proof given here replaces the boundary regularity by an
  even reflection and the weak Harnack inequality.

## Related work

Statements of the weak or strict hot spots property for classes of convex planar domains, each as stated in the
cited work:

- Bañuelos and Burdzy (J. Funct. Anal. 164 (1999)): the three forms HS1, HS2, HS3; obtuse triangles (HS3);
  sufficiently long convex domains with symmetry (HS1).
- Jerison and Nadirashvili (J. Amer. Math. Soc. 13 (2000)): convex planar domains with two orthogonal axes of
  symmetry, every first eigenfunction, no smoothness assumption.
- Atar and Burdzy (J. Amer. Math. Soc. 17 (2004)): lip domains.
- Judge and Mondal (Ann. of Math. 191 (2020), erratum 195 (2022)): no interior critical points on any Euclidean
  triangle. Chen, Gui and Yao ([arXiv:2311.12659](https://arxiv.org/abs/2311.12659)): the non-vertex critical
  points on triangles.
- Steinerberger ([arXiv:1907.13044](https://arxiv.org/abs/1907.13044)): on convex planar domains the extrema lie
  within a universal multiple of the inradius of the endpoints of a diameter.
- Deng, Jiang and Yang ([arXiv:2607.17882](https://arxiv.org/abs/2607.17882)): the hot spots constant of convex
  planar domains with piecewise C^{1,α} boundary is below 1.48.
- Deng, Gui, Jiang, Yang, Yao and Zou ([arXiv:2604.19003](https://arxiv.org/abs/2604.19003)): isosceles
  trapezoids and kites.
- Outside the class considered here: domains with holes (Burdzy and Werner 1999, Burdzy 2005) and convex
  domains in high dimension (de Dios Pont, [arXiv:2412.06344](https://arxiv.org/abs/2412.06344)) can have interior
  extrema.

The paper's introduction gives the precise statements and further references.

## Files

Read [paper.pdf](paper.pdf). To compile the source, with Tectonic installed,

    cd source
    tectonic main.tex

or, with the included bibliography file `main.bbl`, run `pdflatex main.tex` twice. `SHA256SUMS` lists the
checksums of the files in this directory.

## Citation

```bibtex
@misc{Guo2026HotSpotsConvex,
  author = {Guo, Jizhou},
  title = {First {N}eumann eigenfunctions of convex planar domains attain their extrema on the boundary},
  year = {2026},
  month = oct,
  howpublished = {\url{https://github.com/aster2024/openai-math-followups/tree/main/hot-spots-convex-planar}},
  note = {Preprint, 10 October 2026}
}
```
