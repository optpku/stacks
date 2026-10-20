module

public import ReasLib.AlgebraicGeometry.Scheme.PicardStack.InertiaProduct
import StacksCheckRecall

/-!
# Example 95.17.2

The inertia stack of the Picard stack of a morphism of schemes with the
base-change structure-sheaf isomorphism hypothesis is `𝔾ₘ[S] ×_S Pic_{X/S}`.
-/

@[expose] public section

open CategoryTheory
open AlgebraicGeometry
open scoped Bicategory

universe u

namespace AlgebraicGeometry

open StackOver.Groupoids.Hom

/- Example 95.17.2: if `f : X ⟶ S` is a morphism of schemes such that for every
`T ⟶ S` the base change `f_T` has `O_T ⟶ f_{T,*} O_{X_T}` an isomorphism, then
the inertia stack of `picardStack f` is equivalent to `𝔾ₘ[S] ×_S picardStack f`
as a stack in groupoids over `(Sch/S)_fppf`. -/
@[stacks 0375] #check
  (@AlgebraicGeometry.inertia_mulGroupProduct :
    ∀ {X S : Scheme.{u}} (f : X ⟶ S)
      (_ : Scheme.Hom.IsIsoBaseChangeStructurePushforward f),
      IsEquivalence (Picard.inertiaMulGroupHom f))

end AlgebraicGeometry
