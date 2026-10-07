module

public import ReasLib.AlgebraicGeometry.Scheme.FieldExtension.Noetherian
public import ReasLib.AlgebraicGeometry.Scheme.FieldExtension.Stalk.Local
public import ReasLib.RingTheory.CohenMacaulay.Fiber.FieldExtension

/-!
# Cohen--Macaulay stalks under field extension

This file compares Cohen--Macaulayness of stalks at corresponding points of a
scheme and its base change along a field extension.
-/

@[expose] public section

open CategoryTheory
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.FieldExtension.CohenMacaulay

variable {k : Type u} [Field k]
variable {K : Type u} [Field K] [Algebra k K]
variable {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of k))

/-- For an essentially finite type field extension, corresponding points of a
locally Noetherian scheme and its field-extension base change have
Cohen--Macaulay stalks simultaneously. -/
@[stacks 045P]
theorem stalk_iff_of_essFiniteType
    [IsLocallyNoetherian X] [Algebra.EssFiniteType k K]
    (x : X) (x' : FieldExtension.baseChange k K f)
    (hx : FieldExtension.toSource k K f x' = x) :
    Module.CohenMacaulay (X.presheaf.stalk x) (X.presheaf.stalk x) ↔
      let _ : IsLocallyNoetherian (FieldExtension.baseChange k K f) :=
        (Scheme.Hom.isLocallyNoetherian_iff_isLocallyNoetherian_pullback_fieldExtension
          (K := K) f).1 inferInstance
      Module.CohenMacaulay ((FieldExtension.baseChange k K f).presheaf.stalk x')
        ((FieldExtension.baseChange k K f).presheaf.stalk x') := sorry

/-- For a scheme locally of finite type over a field, corresponding points of
the scheme and its base change along any field extension have Cohen--Macaulay
stalks simultaneously. -/
@[stacks 045P]
theorem stalk_iff_of_locallyOfFiniteType
    [LocallyOfFiniteType f]
    (x : X) (x' : FieldExtension.baseChange k K f)
    (hx : FieldExtension.toSource k K f x' = x) :
    let _ : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
    let _ : IsLocallyNoetherian (FieldExtension.baseChange k K f) :=
      LocallyOfFiniteType.isLocallyNoetherian (FieldExtension.toBase k K f)
    Module.CohenMacaulay (X.presheaf.stalk x) (X.presheaf.stalk x) ↔
      Module.CohenMacaulay ((FieldExtension.baseChange k K f).presheaf.stalk x')
        ((FieldExtension.baseChange k K f).presheaf.stalk x') := sorry

end AlgebraicGeometry.FieldExtension.CohenMacaulay
