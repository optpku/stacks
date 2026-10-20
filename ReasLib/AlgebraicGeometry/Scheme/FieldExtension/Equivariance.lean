module

public import Mathlib.AlgebraicGeometry.Pullbacks
public import ReasLib.AlgebraicGeometry.Scheme.FieldExtension.Basic

/-!
# Equivariance of field-extension base change

This leaf lifts an endomorphism of `Spec K` over `Spec k` to the corresponding
field-extension base change.  It is independent of Galois theory and can be
used for arbitrary automorphisms of the extension base.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

noncomputable section

universe u

namespace AlgebraicGeometry

namespace FieldExtension.Equivariance

/-- Lift an endomorphism of `Spec K` that lies over `Spec k` to the field-extension
base change of a scheme over `k`. -/
noncomputable abbrev map
    {k K : Type u} [Field k] [Field K] [Algebra k K]
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of k))
    (g : Spec (CommRingCat.of K) ⟶ Spec (CommRingCat.of K))
    (hg : g ≫ FieldExtension.specMap k K = FieldExtension.specMap k K) :
    FieldExtension.baseChange k K f ⟶ FieldExtension.baseChange k K f :=
  pullback.map
    f
    (FieldExtension.specMap k K)
    f
    (FieldExtension.specMap k K)
    (𝟙 X)
    g
    (𝟙 (Spec (CommRingCat.of k)))
    ((Category.comp_id _).trans (Category.id_comp _).symm)
    ((Category.comp_id _).trans hg.symm)

/-- The composite of two endomorphisms of `Spec K` lying over `Spec k` again lies over `Spec k`. -/
theorem specMap_comp
    (k K : Type u) [Field k] [Field K] [Algebra k K]
    (g₁ g₂ : Spec (CommRingCat.of K) ⟶ Spec (CommRingCat.of K))
    (hg₁ : g₁ ≫ FieldExtension.specMap k K = FieldExtension.specMap k K)
    (hg₂ : g₂ ≫ FieldExtension.specMap k K = FieldExtension.specMap k K) :
    (g₁ ≫ g₂) ≫ FieldExtension.specMap k K = FieldExtension.specMap k K := sorry

/-- The lifted identity endomorphism is the identity on the field-extension base change. -/
theorem map_id
    (k K : Type u) [Field k] [Field K] [Algebra k K]
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of k)) :
    map (k := k) (K := K) f (𝟙 (Spec (CommRingCat.of K)))
        (Category.id_comp _) = 𝟙 _ := sorry

/-- Lifting endomorphisms over the base preserves composition. -/
theorem map_comp
    (k K : Type u) [Field k] [Field K] [Algebra k K]
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of k))
    (g₁ g₂ : Spec (CommRingCat.of K) ⟶ Spec (CommRingCat.of K))
    (hg₁ : g₁ ≫ FieldExtension.specMap k K = FieldExtension.specMap k K)
    (hg₂ : g₂ ≫ FieldExtension.specMap k K = FieldExtension.specMap k K) :
    map f g₁ hg₁ ≫ map f g₂ hg₂ =
      map f (g₁ ≫ g₂) (specMap_comp k K g₁ g₂ hg₁ hg₂) := sorry

/-- The lifted endomorphism commutes with the projection to the source scheme. -/
theorem map_toSource
    (k K : Type u) [Field k] [Field K] [Algebra k K]
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of k))
    (g : Spec (CommRingCat.of K) ⟶ Spec (CommRingCat.of K))
    (hg : g ≫ FieldExtension.specMap k K = FieldExtension.specMap k K) :
    map f g hg ≫ FieldExtension.toSource k K f =
      FieldExtension.toSource k K f := sorry

/-- The lifted endomorphism commutes with the projection to the extension base. -/
theorem map_toBase
    (k K : Type u) [Field k] [Field K] [Algebra k K]
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of k))
    (g : Spec (CommRingCat.of K) ⟶ Spec (CommRingCat.of K))
    (hg : g ≫ FieldExtension.specMap k K = FieldExtension.specMap k K) :
    map f g hg ≫ FieldExtension.toBase k K f =
      FieldExtension.toBase k K f ≫ g := sorry

end FieldExtension.Equivariance

end AlgebraicGeometry
