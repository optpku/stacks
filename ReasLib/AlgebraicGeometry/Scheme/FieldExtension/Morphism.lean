module

public import ReasLib.AlgebraicGeometry.Scheme.FieldExtension.Over

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.FieldExtension

/-- The base change of `g : T ⟶ S` along `Spec L ⟶ Spec K`, as a morphism
`T_L ⟶ S_L` of field-extension pullbacks. -/
abbrev baseChangeHom (K L : Type u) [Field K] [Field L] [Algebra K L]
    {T S : Scheme.{u}} (s : S ⟶ Spec (CommRingCat.of K)) (g : T ⟶ S) :
    baseChange K L (g ≫ s) ⟶ baseChange K L s :=
  ((Over.functor K L).map
    (CategoryTheory.Over.homMk g rfl :
      CategoryTheory.Over.mk (g ≫ s) ⟶ CategoryTheory.Over.mk s)).left

/-- `baseChangeHom` is the underlying scheme morphism of the image of `g` under
`FieldExtension.Over.functor`. -/
theorem baseChangeHom_eq (K L : Type u) [Field K] [Field L] [Algebra K L]
    {T S : Scheme.{u}} (s : S ⟶ Spec (CommRingCat.of K)) (g : T ⟶ S) :
    baseChangeHom K L s g =
      ((Over.functor K L).map
        (CategoryTheory.Over.homMk g rfl :
          CategoryTheory.Over.mk (g ≫ s) ⟶ CategoryTheory.Over.mk s)).left := rfl

/-- The field-extension base change of `g` commutes with projection to the source
schemes. -/
theorem baseChangeHom_toSource (K L : Type u) [Field K] [Field L] [Algebra K L]
    {T S : Scheme.{u}} (s : S ⟶ Spec (CommRingCat.of K)) (g : T ⟶ S) :
    baseChangeHom K L s g ≫ toSource K L s = toSource K L (g ≫ s) ≫ g := sorry

/-- The field-extension base change of `g` commutes with projection to `Spec L`. -/
theorem baseChangeHom_toBase (K L : Type u) [Field K] [Field L] [Algebra K L]
    {T S : Scheme.{u}} (s : S ⟶ Spec (CommRingCat.of K)) (g : T ⟶ S) :
    baseChangeHom K L s g ≫ toBase K L s = toBase K L (g ≫ s) := sorry

/-- The commutative square of `g` and its field-extension base change is cartesian. -/
theorem baseChangeHom_isPullback (K L : Type u) [Field K] [Field L] [Algebra K L]
    {T S : Scheme.{u}} (s : S ⟶ Spec (CommRingCat.of K)) (g : T ⟶ S) :
    IsPullback (toSource K L (g ≫ s)) (baseChangeHom K L s g) g (toSource K L s) :=
  (IsPullback.of_right
      ((baseChangeHom_toBase K L s g).symm ▸
        (IsPullback.of_hasPullback (g ≫ s) (specMap K L)).flip)
      (baseChangeHom_toSource K L s g)
      (IsPullback.of_hasPullback s (specMap K L)).flip).flip

end AlgebraicGeometry.FieldExtension

end
