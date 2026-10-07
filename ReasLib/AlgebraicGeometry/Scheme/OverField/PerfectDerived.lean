module

public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.Perfect.Triangulated
public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.Perfect.Linear
public import ReasLib.AlgebraicGeometry.Scheme.OverField
public import ReasLib.CategoryTheory.Linear.Opposite
public import ReasLib.CategoryTheory.Pretriangulated.Homological.Opposite
public import Mathlib.CategoryTheory.Linear.Yoneda
public import Mathlib.CategoryTheory.Triangulated.Opposite.Pretriangulated

@[expose] public section

open AlgebraicGeometry CategoryTheory
open AlgebraicGeometry.RingedSpace

noncomputable section

universe u

namespace AlgebraicGeometry.SchemeOverField

/-- The `X`-indexed perfect derived category of `𝒪_X`-modules. -/
@[reducible]
def PerfectDerived {k : Type u} [Field k] (X : SchemeOverField k) :=
  @RingedSpace.ModuleDerived.Perfect X.left.toRingedSpace

namespace PerfectDerived

/-- The explicit `k`-linear structure on the ambient derived category induced by `X.hom`. -/
@[reducible]
noncomputable def ambientLinear
    {k : Type u} [Field k] (X : SchemeOverField k) :
    Linear k (RingedSpace.ModuleDerived X.left.toRingedSpace) :=
  @DerivedCategory.instLinear k _ X.left.toRingedSpace.Modules _ _
    (Linear.ofRingMorphism
      ((RingedSpace.GlobalSections.centerHom X.left.toRingedSpace).comp
        (Scheme.Hom.globalSectionsMap X.hom))) _

/-- The inclusion of `X`-indexed perfect derived objects into the ambient derived category. -/
abbrev inclusion {k : Type u} [Field k] (X : SchemeOverField k) :
    PerfectDerived X ⥤ RingedSpace.ModuleDerived X.left.toRingedSpace :=
  RingedSpace.ModuleDerived.Perfect.ι

/-- The canonical `k`-linear structure on the `X`-indexed perfect derived category. -/
noncomputable instance instLinear {k : Type u} [Field k] (X : SchemeOverField k) :
    Linear k (PerfectDerived X) :=
  Scheme.ModuleDerived.Perfect.linearFor X.hom

/-- The representable `k`-linear functor `E ↦ Hom_X(E, K)` on perfect derived objects. -/
noncomputable def representedBy
    {k : Type u} [Field k] (X : SchemeOverField k)
    (K : RingedSpace.ModuleDerived X.left.toRingedSpace) :
    (PerfectDerived X)ᵒᵖ ⥤ ModuleCat k :=
  (inclusion X).op ⋙
    (@linearYoneda k _ (RingedSpace.ModuleDerived X.left.toRingedSpace) _ _
      (ambientLinear X)).obj K

/-- Evaluation of `representedBy X K` at a perfect object is the corresponding derived Hom module. -/
theorem representedBy_obj
    {k : Type u} [Field k] (X : SchemeOverField k)
    (K : RingedSpace.ModuleDerived X.left.toRingedSpace)
    (E : PerfectDerived X) :
    (representedBy X K).obj (Opposite.op E) =
      @ModuleCat.of k _ (E.obj ⟶ K) _ ((ambientLinear X).homModule E.obj K) := sorry

end PerfectDerived

end AlgebraicGeometry.SchemeOverField

end
