module

public import ReasLib.AlgebraicGeometry.Polarized
import StacksCheckRecall

/-!
# The stack of polarized proper schemes

Situation 99.14.1 introduces the category of pairs consisting of a proper flat
finite-presentation morphism of schemes and a relatively ample invertible
module on the source.
-/

@[expose] public section

universe u

/- Situation 99.14.1: the category Polarized of pairs `(X ⟶ S, L)` where
`X ⟶ S` is a proper, flat, finite-presentation morphism of schemes and `L` is
an invertible `O_X`-module which is relatively ample on `X / S`. A morphism
`(X' ⟶ S', L') ⟶ (X ⟶ S, L)` is a triple `(f, g, φ)` with `f : X' ⟶ X` and
`g : S' ⟶ S` forming a cartesian square and `φ : f^* L ≅ L'` an isomorphism.
The forgetful functor `p : Polarized ⥤ Scheme`, `(X ⟶ S, L) ↦ S`, presents
Polarized as a category over `Sch_fppf`. -/
@[stacks 0D1M] #check (AlgebraicGeometry.Polarized.over :
  CategoryTheory.BasedCategory.{u, u + 1} AlgebraicGeometry.Scheme.{u})
