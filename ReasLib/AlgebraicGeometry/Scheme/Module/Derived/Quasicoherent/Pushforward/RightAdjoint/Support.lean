/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Noetherian
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.FinitePresentation
public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.Quasicoherent.BaseChange.Support
public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.Quasicoherent.Pushforward.RightAdjoint.Coproduct

@[expose] public section

open AlgebraicGeometry CategoryTheory
open DerivedCategory.TStructure

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.DerivedQCoh

/-- A proper morphism that is flat and of finite presentation, or has Noetherian
target, preserves bounded-below support away from quasi-compact opens under its
derived quasicoherent right adjoint. -/
theorem supportOnComplement_boundedBelow_of_proper_of_flat_or_noetherian
    {X Y : Scheme.{u}} [CompactSpace Y] [QuasiSeparatedSpace Y]
    (f : X ⟶ Y) [IsProper f]
    (a : DerivedQCoh Y ⥤ DerivedQCoh X)
    (aAdjunction : pushforwardCohomologyIn f ⊣ a)
    (h_finiteness : (Flat f ∧ Scheme.Hom.FinitePresentation f) ∨ IsNoetherian Y)
    (V : Y.Opens) (hV : IsCompact (V : Set Y)) (Q : DerivedQCoh Y)
    (hQ_boundedBelow :
      (t.plus : ObjectProperty (RingedSpace.ModuleDerived Y.toRingedSpace)) Q.obj)
    (hQ_support : RingedSpace.ModuleDerived.IsSupportedOn Q.obj (V : Set Y)ᶜ) :
    RingedSpace.ModuleDerived.IsSupportedOn
      (a.obj Q).obj (f ⁻¹ᵁ V : Set X)ᶜ := sorry

/-- A right adjoint to derived quasicoherent pushforward along a perfect proper morphism of
Noetherian schemes sends objects supported on a closed subset to objects supported on its
inverse image. -/
theorem rightAdjoint_isSupportedOn_preimage_of_perfect_proper
    {X Y : Scheme.{u}} [IsNoetherian X] [IsNoetherian Y]
    (f : X ⟶ Y) [IsProper f] [LocallyOfType RingHom.IsPerfectRingMap f]
    (a : DerivedQCoh Y ⥤ DerivedQCoh X)
    (aAdjunction : pushforwardCohomologyIn f ⊣ a)
    (T : TopologicalSpace.Closeds Y) (Q : DerivedQCoh Y)
    (hQ : RingedSpace.ModuleDerived.IsSupportedOn Q.obj (T : Set Y)) :
    RingedSpace.ModuleDerived.IsSupportedOn
      (a.obj Q).obj (T.preimage f.continuous : Set X) := sorry

/-- A right adjoint to derived quasicoherent pushforward along a proper, flat morphism of
finite presentation over a quasi-compact quasi-separated scheme sends objects supported on
a closed subset to objects supported on its inverse image. -/
theorem rightAdjoint_isSupportedOn_preimage_of_proper_flat
    {X Y : Scheme.{u}} [CompactSpace Y] [QuasiSeparatedSpace Y]
    (f : X ⟶ Y) [IsProper f] [Flat f] [Scheme.Hom.FinitePresentation f]
    (a : DerivedQCoh Y ⥤ DerivedQCoh X)
    (aAdjunction : pushforwardCohomologyIn f ⊣ a)
    (T : TopologicalSpace.Closeds Y) (Q : DerivedQCoh Y)
    (hQ : RingedSpace.ModuleDerived.IsSupportedOn Q.obj (T : Set Y)) :
    RingedSpace.ModuleDerived.IsSupportedOn
      (a.obj Q).obj (T.preimage f.continuous : Set X) := sorry

end AlgebraicGeometry.Scheme.DerivedQCoh
