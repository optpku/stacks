module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Groupoid.Quotient.Descent

/-!
# Explicit description of objects of a quotient stack

This file records the six clauses of Lemma 78.24.1: fibre objects of `[U/R]` are fppf-locally
in the image of `π`, the overlap isomorphisms are `π(r_ij)`, the resulting `(u_i, r_ij)` is a
`[U/R]`-descent datum, every such datum is effective, fibre morphisms biject with morphisms of
descent data, and the correspondence is compatible with refinements.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicSpace GroupoidAlgebraicSpace Limits

open CategoryTheory.Functor

noncomputable section

universe u

/- Lemma 78.24.1 (1). Assume `B → S` and `(U, R, s, t, c)` are as in Definition 78.20.1 (1),
and let `π : 𝒮_U ⟶ [U/R]` be as in Lemma 78.20.2. Let `T` be a scheme over `S`. For every
object `x` of the fibre category `[U/R]_T` there exists an fppf covering `{f_i : T_i ⟶ T}`
such that `f_i^* x ≅ π(u_i)` for some `u_i ∈ U(T_i)`. -/
@[stacks 044X] #check (AlgebraicGeometry.GroupoidAlgebraicSpace.exists_fppfCovering_atlasIso :
    ∀ {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) {T : Over S} (x : (fppfQuotientStack G).p.Fiber T),
    ∃ (ι : Type u) (family : ι → Over T.left)
      (u : ∀ i, ofOver (coverOver family i) ⟶ G.U.left),
      Scheme.FppfCovering family ∧
        ∀ i, Nonempty (atlasObj G (u i) ≅ Chosen.reindexObj (fppfQuotientStack G).p (coverHom family i) x))

/- Lemma 78.24.1 (2). In the situation of (1), the composition of the isomorphisms
`π(u_i ∘ pr₀) = pr₀^* π(u_i) ≅ pr₀^* f_i^* x ≅ pr₁^* f_j^* x ≅ pr₁^* π(u_j) = π(u_j ∘ pr₁)`
is of the form `π(r_ij)` for morphisms `r_ij : T_i ×_T T_j ⟶ R`. -/
@[stacks 044X] #check (AlgebraicGeometry.GroupoidAlgebraicSpace.exists_arrow_of_composedIso :
    ∀ {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) {T : Over S} {ι : Type u} (family : ι → Over T.left)
    (x : (fppfQuotientStack G).p.Fiber T)
    (u : ∀ i, ofOver (coverOver family i) ⟶ G.U.left)
    (e : ∀ i, atlasObj G (u i) ≅ Chosen.reindexObj (fppfQuotientStack G).p (coverHom family i) x),
    ∃ r : ∀ i j, ofOver (pairOver family i j) ⟶ G.R.left,
      ∀ i j, IsPiArrow G family x u e (r i j))

/- Lemma 78.24.1 (3). In the situation of (1) and (2), the system `(u_i, r_ij)` forms a
`[U/R]`-descent datum. -/
@[stacks 044X] #check (AlgebraicGeometry.GroupoidAlgebraicSpace.isDescentDatum_of_atlasIso :
    ∀ {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) {T : Over S} {ι : Type u} (family : ι → Over T.left)
    (x : (fppfQuotientStack G).p.Fiber T)
    (u : ∀ i, ofOver (coverOver family i) ⟶ G.U.left)
    (e : ∀ i, atlasObj G (u i) ≅ Chosen.reindexObj (fppfQuotientStack G).p (coverHom family i) x)
    (r : ∀ i j, ofOver (pairOver family i j) ⟶ G.R.left)
    (hπ : ∀ i j, IsPiArrow G family x u e (r i j)),
    ∃ D : DescentDatum G family, D.u = u ∧ D.r = r)

/- Lemma 78.24.1 (4). Any `[U/R]`-descent datum `(u_i, r_ij)` relative to an fppf covering
of `T` arises from an object of `[U/R]_T` as in (1)–(3). -/
@[stacks 044X] #check (AlgebraicGeometry.GroupoidAlgebraicSpace.exists_fiberObj_of_descentDatum :
    ∀ {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) {T : Over S} {ι : Type u} (family : ι → Over T.left)
    (h_covering : Scheme.FppfCovering family) (D : DescentDatum G family),
    ∃ x : (fppfQuotientStack G).p.Fiber T, Nonempty (Corresponds G family x D))

/- Lemma 78.24.1 (5). If `x` corresponds to `(u_i, r_ij)` and `y` corresponds to
`(u'_i, r'_ij)` relative to an fppf covering `{f_i : T_i ⟶ T}`, there is a canonical
bijection `Mor_{[U/R]_T}(x, y) ↔` morphisms of `[U/R]`-descent data
`(u_i, r_ij) ⟶ (u'_i, r'_ij)`. -/
@[stacks 044X] #check (AlgebraicGeometry.GroupoidAlgebraicSpace.fiberHom_existsUnique :
    ∀ {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) {T : Over S} {ι : Type u} (family : ι → Over T.left)
    (h_covering : Scheme.FppfCovering family)
    {x y : (fppfQuotientStack G).p.Fiber T} {D D' : DescentDatum G family}
    (hx : Corresponds G family x D) (hy : Corresponds G family y D'),
    (∀ φ : x ⟶ y, ∃! ψ : DescentDatum.Hom D D', ψ.agreesWith hx hy φ) ∧
      ∀ ψ : DescentDatum.Hom D D', ∃! φ : x ⟶ y, ψ.agreesWith hx hy φ)

/- Lemma 78.24.1 (6). The correspondence of (1)–(5) is compatible with refinements of fppf
coverings: if `x` corresponds to `D` on an fppf covering `family`, then `x` corresponds to the
pullback of `D` along a refinement to another fppf covering `family'`, and agreement of descent
morphisms with fibre morphisms is stable in both directions under the same pullback. -/
@[stacks 044X] #check (AlgebraicGeometry.GroupoidAlgebraicSpace.corresponds_pullback :
    ∀ {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) {T : Over S} {ι : Type u} (family : ι → Over T.left)
    (h_covering : Scheme.FppfCovering family)
    {x : (fppfQuotientStack G).p.Fiber T} {D : DescentDatum G family}
    (hx : Corresponds G family x D) {ι' : Type u} (family' : ι' → Over T.left)
    (h_covering' : Scheme.FppfCovering family')
    (α : ι' → ι) (φ : ∀ j, family' j ⟶ family (α j)),
    (∀ {y : (fppfQuotientStack G).p.Fiber T} {D' : DescentDatum G family}
        (hy : Corresponds G family y D') (φhom : x ⟶ y) (ψ : DescentDatum.Hom D D'),
        ψ.agreesWith hx hy φhom →
          (ψ.pullback α φ).agreesWith (hx.pullback α φ) (hy.pullback α φ) φhom) ∧
      ∀ {y : (fppfQuotientStack G).p.Fiber T} {D' : DescentDatum G family}
        (hy : Corresponds G family y D') (φhom : x ⟶ y) (ψ : DescentDatum.Hom D D'),
        (ψ.pullback α φ).agreesWith (hx.pullback α φ) (hy.pullback α φ) φhom →
          ψ.agreesWith hx hy φhom)
