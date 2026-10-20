/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.ProjectiveSpectrum.DegreeOpenFactorization
public import Mathlib.AlgebraicGeometry.Sites.Representability
public import Mathlib.CategoryTheory.RepresentedBy

/-!
# Functors presented by the fixed-degree opens of a projective spectrum

An explicit presentation records a Zariski sheaf, its positive-degree charts, and the comparison
between its values on quasi-compact schemes and factorizations through fixed-degree opens.
-/

@[expose] public section

open CategoryTheory Opposite

noncomputable section

universe u v

namespace AlgebraicGeometry.Proj

variable {A : Type u} {σ : Type v} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
variable (𝒜 : ℕ → σ) [GradedRing 𝒜]

/-- An explicit Zariski-sheaf presentation by the positive-degree opens of `Proj 𝒜`. -/
structure MorphismFunctor where
  /-- The presented contravariant functor, equipped with its Zariski sheaf property. -/
  toSheaf : Sheaf Scheme.zariskiTopology (Type u)
  /-- The canonical map from each positive-degree open into the presented functor. -/
  degreeToFunctor :
    ∀ d : {n : ℕ // 1 ≤ n}, yoneda.obj ((degreeOpen 𝒜 d.1).toScheme) ⟶ toSheaf.1
  /-- Each positive-degree chart is a relatively representable open immersion. -/
  degreeToFunctor_isOpenImmersion :
    ∀ d : {n : ℕ // 1 ≤ n}, IsOpenImmersion.presheaf (degreeToFunctor d)
  /-- The positive-degree charts jointly cover the presented functor. -/
  coveredByDegree :
    Presheaf.IsLocallySurjective Scheme.zariskiTopology (Limits.Sigma.desc degreeToFunctor)
  /-- On a quasi-compact scheme, the presented functor is the type of degree-open
  factorization classes. -/
  objEquiv :
    ∀ (Y : Schemeᵒᵖ), CompactSpace Y.unop.carrier →
      toSheaf.1.obj Y ≃ (degreeOpenFactorizationFunctor 𝒜).obj Y
  /-- Under the quasi-compact comparison, a chart element is its degree-open factorization
  class. -/
  degreeToFunctor_compatibility :
    ∀ (d : {n : ℕ // 1 ≤ n}) (Y : Scheme.{u})
      (hYCompact : CompactSpace Y.carrier) (f : Y ⟶ (degreeOpen 𝒜 d.1).toScheme),
      objEquiv (Opposite.op Y) hYCompact ((degreeToFunctor d).app (Opposite.op Y) f) =
        Quotient.mk (DegreeOpenFactorization.setoid 𝒜 Y)
          ({ degree := d.1, positive := d.2, map := f } : DegreeOpenFactorization 𝒜 Y)
  /-- The quasi-compact comparisons commute with pullback along morphisms of test schemes. -/
  objEquiv_naturality :
    ∀ {Y Z : Schemeᵒᵖ} (hYCompact : CompactSpace Y.unop.carrier)
      (hZCompact : CompactSpace Z.unop.carrier) (f : Y ⟶ Z) (x : toSheaf.1.obj Y),
      objEquiv Z hZCompact (toSheaf.1.map f x) =
        (degreeOpenFactorizationFunctor 𝒜).map f (objEquiv Y hYCompact x)

namespace MorphismFunctor

/-- The contravariant type-valued functor underlying a degree-open presentation. -/
abbrev toFunctor (F : MorphismFunctor 𝒜) : Schemeᵒᵖ ⥤ Type u :=
  F.toSheaf.1

/-- Transport a degree-open presentation across an isomorphism of its underlying functor. -/
def ofIso (F : MorphismFunctor 𝒜) (G : Sheaf Scheme.zariskiTopology (Type u))
    (e : F.toFunctor ≅ G.1) : MorphismFunctor 𝒜 where
  toSheaf := G
  degreeToFunctor d := F.degreeToFunctor d ≫ e.hom
  degreeToFunctor_isOpenImmersion := sorry
  coveredByDegree := sorry
  objEquiv Y hYCompact := (e.symm.app Y).toEquiv.trans (F.objEquiv Y hYCompact)
  degreeToFunctor_compatibility := sorry
  objEquiv_naturality := sorry

/-- The scheme `Proj 𝒜` represents the functor carried by a degree-open presentation. -/
theorem isRepresentedBy (F : MorphismFunctor 𝒜) :
    ∃ x : F.toFunctor.obj (Opposite.op (Proj 𝒜)), F.toFunctor.IsRepresentedBy x := sorry

end MorphismFunctor

end AlgebraicGeometry.Proj
