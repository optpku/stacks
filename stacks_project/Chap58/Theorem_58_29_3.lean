/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Etale.AffineLocus
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry CategoryTheory
open scoped AlgebraicGeometry

universe u

/- Theorem 58.29.3: if `Y` is an excellent regular scheme over a field, `f : X ⟶ Y`
is of finite type, and `X` is normal, then the inclusion of the maximal open
`V := MorphismProperty.sourceLocus (fun ⦃X Y : Scheme⦄ (g : X ⟶ Y) ↦ Etale g) f ⊂ X`
on which `f` is étale is an affine morphism. -/
@[stacks 0ECD] #check (AlgebraicGeometry.Scheme.Hom.isAffineHom_etaleSourceLocus_ι :
    ∀ {k : Type u} [Field k] {Y : Scheme.{u}} [Scheme.Regular Y]
    [Y.HasRingPropertyLocally (fun A : CommRingCat.{u} ↦ IsExcellentRing A)]
    (hY : Y ⟶ Spec (CommRingCat.of k)) {X : Scheme.{u}} (f : X ⟶ Y)
    [Scheme.Hom.FiniteType f] (hX : X.isNormal),
    IsAffineHom
      (MorphismProperty.sourceLocus (fun ⦃X Y : Scheme.{u}⦄ (g : X ⟶ Y) ↦ Etale g) f).ι)
