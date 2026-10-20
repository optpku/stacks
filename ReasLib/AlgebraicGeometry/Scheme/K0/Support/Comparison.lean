/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.Perfect.Regular
public import ReasLib.AlgebraicGeometry.Scheme.K0.Support
public import ReasLib.AlgebraicGeometry.Scheme.K0.Support.Euler
public import ReasLib.CategoryTheory.ObjectProperty.FullSubcategory.Restriction
public import ReasLib.AlgebraicGeometry.Scheme.K0.CoherentSupport

/-!
# Supported coherent-to-perfect comparison

This module constructs the degree-zero comparison from the Grothendieck group of coherent
sheaves supported on a subset to the triangulated Grothendieck group of perfect complexes
with the same support.
-/

@[expose] public section

open CategoryTheory

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.K0'WithSupport

variable (X : Scheme.{u}) [IsLocallyNoetherian X] (T : Set X)

/-- The degree-zero realization of a coherent sheaf is perfect on a regular scheme. -/
theorem single_isPerfect [Scheme.Regular X]
    (F : RingedSpace.CohSupportedOn X.toRingedSpace T) :
    RingedSpace.ModuleDerived.IsPerfect
      ((DerivedCategory.singleFunctor X.Modules (0 : ℤ)).obj F.obj.obj) := sorry

/-- The degree-zero realization of a supported coherent sheaf has the same support bound. -/
theorem single_isSupportedOn
    (F : RingedSpace.CohSupportedOn X.toRingedSpace T) :
    RingedSpace.ModuleDerived.IsSupportedOn
      ((DerivedCategory.singleFunctor X.Modules (0 : ℤ)).obj F.obj.obj) T := sorry

/-- The functor sending a supported coherent sheaf to its degree-zero supported perfect
derived realization. -/
noncomputable def singlePerfect [Scheme.Regular X] :
    RingedSpace.CohSupportedOn X.toRingedSpace T ⥤
      RingedSpace.ModuleDerived.PerfectSupportedOn T :=
  ObjectProperty.FullSubcategory.restrict
    ((SheafOfModules.isCoherent X.toRingedSpace.ringCatSheaf).ι ⋙
      DerivedCategory.singleFunctor X.Modules (0 : ℤ))
    (fun F hF ↦ (RingedSpace.ModuleDerived.perfectSupportedOn_iff T _).2
      ⟨single_isPerfect X T ⟨F, hF⟩, single_isSupportedOn X T ⟨F, hF⟩⟩)

/-- The underlying derived object of `singlePerfect X T` is the degree-zero realization. -/
theorem singlePerfect_obj [Scheme.Regular X]
    (F : RingedSpace.CohSupportedOn X.toRingedSpace T) :
    ((singlePerfect X T).obj F).obj =
      (DerivedCategory.singleFunctor X.Modules (0 : ℤ)).obj F.obj.obj := sorry

/-- Degree-zero supported-perfect classes kill the short-exact relations defining
`K0'WithSupport X T`. -/
theorem relations_le_ker_toPerfect [Scheme.Regular X] :
    AbelianK0.relations (RingedSpace.CohSupportedOn X.toRingedSpace T) ≤
      (FreeAbelianGroup.lift fun F : RingedSpace.CohSupportedOn X.toRingedSpace T ↦
        TriangulatedK0.of ((singlePerfect X T).obj F)).ker := sorry

/-- The comparison homomorphism from supported coherent `K₀` to supported perfect `K₀`. -/
noncomputable def toPerfect [Scheme.Regular X] :
    K0'WithSupport X T →+ K0WithSupport X T :=
  AbelianK0.lift
    (fun F ↦ TriangulatedK0.of ((singlePerfect X T).obj F))
    (relations_le_ker_toPerfect X T)

/-- The supported comparison sends a coherent generator to its degree-zero perfect class. -/
theorem toPerfect_of [Scheme.Regular X]
    (F : RingedSpace.CohSupportedOn X.toRingedSpace T) :
    toPerfect X T (of X T F) =
      TriangulatedK0.of ((singlePerfect X T).obj F) := sorry

end AlgebraicGeometry.Scheme.K0'WithSupport

namespace AlgebraicGeometry.Scheme.K0'

variable {X Z : Scheme.{u}} [IsLocallyNoetherian X] [Scheme.Regular X]

/-- A closed immersion into a regular locally Noetherian scheme induces a comparison from
coherent `K₀` of the closed subscheme to perfect `K₀` supported on its image. -/
noncomputable def toK0WithSupport (i : Z ⟶ X) [IsClosedImmersion i] :
    @K0' Z (LocallyOfFiniteType.isLocallyNoetherian i) →+
      K0WithSupport X (Set.range i.base) :=
  (K0'WithSupport.toPerfect X (Set.range i.base)).comp
    (K0'WithSupport.closedPushforward i)

/-- The closed-immersion comparison sends a coherent generator to the degree-zero class of
its supported pushforward. -/
theorem toK0WithSupport_of (i : Z ⟶ X) [IsClosedImmersion i]
    (F : RingedSpace.Coh Z.toRingedSpace) :
    toK0WithSupport i
        (ObjectProperty.GrothendieckGroup.of
          (SheafOfModules.isCoherent Z.toRingedSpace.ringCatSheaf) F) =
      TriangulatedK0.of
        ((K0'WithSupport.singlePerfect X (Set.range i.base)).obj
          ((@Modules.ClosedImmersion.toSupported X Z _
            (LocallyOfFiniteType.isLocallyNoetherian i) i _).obj F)) := sorry

section LocallyNoetherian

variable {X Z : Scheme.{u}} [IsLocallyNoetherian X]

/-- The Euler homomorphism followed by the inverse of coherent closed pushforward. -/
noncomputable def fromK0WithSupport (i : Z ⟶ X) [IsClosedImmersion i] :
    K0WithSupport X (Set.range i.base) →+
      @K0' Z (LocallyOfFiniteType.isLocallyNoetherian i) :=
  (AddMonoidHom.inverse
      (K0'WithSupport.closedPushforward i)
      (Function.invFun (K0'WithSupport.closedPushforward i))
      (Function.leftInverse_invFun (K0'WithSupport.closedPushforward_bijective i).injective)
      (Function.rightInverse_invFun (K0'WithSupport.closedPushforward_bijective i).surjective)).comp
    (K0WithSupport.toCoherent X (Set.range i.base))

/-- Coherent closed pushforward of `fromK0WithSupport i x` is the Euler class of `x`. -/
theorem closedPushforward_fromK0WithSupport (i : Z ⟶ X) [IsClosedImmersion i]
    (x : K0WithSupport X (Set.range i.base)) :
    K0'WithSupport.closedPushforward i (fromK0WithSupport i x) =
      K0WithSupport.toCoherent X (Set.range i.base) x := sorry

/-- A coherent class with the prescribed closed pushforward is uniquely
`fromK0WithSupport i x`. -/
theorem fromK0WithSupport_unique (i : Z ⟶ X) [IsClosedImmersion i]
    (x : K0WithSupport X (Set.range i.base))
    (z : @K0' Z (LocallyOfFiniteType.isLocallyNoetherian i))
    (hz : K0'WithSupport.closedPushforward i z =
      K0WithSupport.toCoherent X (Set.range i.base) x) :
    z = fromK0WithSupport i x := sorry

end LocallyNoetherian

variable {X Z : Scheme.{u}} [IsNoetherian X] [Scheme.Regular X]

/-- The supported-perfect comparison followed by the Euler/closed-pushforward inverse is
the identity on coherent `K₀` of the closed subscheme. -/
theorem fromK0WithSupport_toK0WithSupport (i : Z ⟶ X) [IsClosedImmersion i]
    (x : @K0' Z (LocallyOfFiniteType.isLocallyNoetherian i)) :
    fromK0WithSupport i (toK0WithSupport i x) = x := sorry

/-- The Euler/closed-pushforward inverse followed by the supported-perfect comparison is
the identity on supported perfect `K₀`. -/
theorem toK0WithSupport_fromK0WithSupport (i : Z ⟶ X) [IsClosedImmersion i]
    (y : K0WithSupport X (Set.range i.base)) :
    toK0WithSupport i (fromK0WithSupport i y) = y := sorry

/-- A closed immersion into a Noetherian regular scheme induces an additive equivalence
between coherent `K₀` of the source and perfect `K₀` supported on its image. -/
noncomputable def equivK0WithSupport (i : Z ⟶ X) [IsClosedImmersion i] :
    @K0' Z (LocallyOfFiniteType.isLocallyNoetherian i) ≃+
      K0WithSupport X (Set.range i.base) where
  toFun := toK0WithSupport i
  invFun := fromK0WithSupport i
  left_inv := fromK0WithSupport_toK0WithSupport i
  right_inv := toK0WithSupport_fromK0WithSupport i
  map_add' := (toK0WithSupport i).map_add

/-- The forward map of `equivK0WithSupport i` is `toK0WithSupport i`. -/
theorem equivK0WithSupport_apply (i : Z ⟶ X) [IsClosedImmersion i]
    (x : @K0' Z (LocallyOfFiniteType.isLocallyNoetherian i)) :
    equivK0WithSupport i x = toK0WithSupport i x := sorry

/-- The inverse map of `equivK0WithSupport i` is `fromK0WithSupport i`. -/
theorem equivK0WithSupport_symm_apply (i : Z ⟶ X) [IsClosedImmersion i]
    (y : K0WithSupport X (Set.range i.base)) :
    (equivK0WithSupport i).symm y = fromK0WithSupport i y := sorry

end AlgebraicGeometry.Scheme.K0'
