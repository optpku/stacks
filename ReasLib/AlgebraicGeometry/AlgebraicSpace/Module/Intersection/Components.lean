/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.RingTheory.Length
public import Mathlib.Topology.Sober
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.ClosedSubspace.Integral
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Intersection.Number
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Stalk

/-!
# Intersection numbers and irreducible components

This file records the decomposition of an intersection number into the
contributions of the top-dimensional irreducible components of a closed
subspace proper over a field.
-/

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace CategoryTheory
open CategoryTheory.MonoidalCategory TopologicalSpace
open scoped AlgebraicGeometry BigOperators

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Modules
namespace Intersection

-- Local instance justification (defeq pin): `HasInjectiveResolutions` and `higherDirectImage` pin the Abelian-induced `Preadditive`/`HasZeroMorphisms` instances for defeq of `higherDirectImage`.
attribute [local instance 2000] Abelian.toPreadditive Preadditive.preadditiveHasZeroMorphisms

/-- The intersection number of invertible modules with a closed subspace proper
over a field is the multiplicity-weighted sum of the intersection numbers of an
explicit finite, injective, and exhaustive family of its top-dimensional
integral closed subspaces. Each multiplicity is the length of the stalk of the
pushed-forward structure module at the corresponding geometric generic point. -/
theorem number_eq_sum_irreducibleComponents {k : Type u} [Field k]
    {X Z : AlgebraicSpace (Spec (CommRingCat.of k))} (i : Z ⟶ X)
    [IsClosedImmersion i] [Proper (SchemeRealization.toBase X)] [IsDecent X]
    [IsLocallyNoetherian X] [IsLocallyNoetherian Z] {d : ℕ}
    (hZdim : dimension Z = d)
    [Abelian X.Modules] [Abelian Z.Modules]
    [Abelian (ofOver (Over.mk (𝟙 (Spec (CommRingCat.of k))))).Modules]
    [HasInjectiveResolutions X.Modules] [HasInjectiveResolutions Z.Modules]
    (L : Fin d → X.Modules) [∀ j : Fin d, isInvertibleObject (L j)]
    {ι : Type u} [Fintype ι]
    {Zi : ι → AlgebraicSpace (Spec (CommRingCat.of k))}
    (iZ : (a : ι) → Zi a ⟶ X)
    [∀ a, IsClosedImmersion (iZ a)] [∀ a, IsIntegral (Zi a)]
    [∀ a, IsLocallyNoetherian (Zi a)] [∀ a, Abelian (Zi a).Modules]
    [∀ a, HasInjectiveResolutions (Zi a).Modules]
    (xbar : ι → GeometricPoint X)
    (h_generic : ∀ a, IsGenericPoint (xbar a).image (Set.range (Points.map (iZ a))))
    (h_component : ∀ a,
      Maximal (fun s : Set (Points X) ↦
          _root_.IsIrreducible s ∧ s ⊆ Set.range (Points.map i))
        (Set.range (Points.map (iZ a))))
    (h_dim : ∀ a, dimension (Zi a) = d)
    (h_injective : Function.Injective fun a ↦ Set.range (Points.map (iZ a)))
    (h_exhaustive : ∀ T : IrreducibleCloseds (Points X),
      Maximal (fun s : Set (Points X) ↦
          _root_.IsIrreducible s ∧ s ⊆ Set.range (Points.map i))
          T.carrier →
        dimension (ClosedSubspace.ofIrreducibleClosed T).X = d →
          ∃ a, Set.range (Points.map (iZ a)) = T.carrier)
    (m : ι → ℕ)
    (h_length : ∀ a,
      Module.length (etaleLocalRing X (xbar a))
          (stalkModuleCat (xbar a)
            ((AlgebraicSpace.Modules.pushforward i).obj
              (SheafOfModules.unit (structureSheaf Z) : Z.Modules))) =
        m a) :
    number i hZdim L = ∑ a : ι, (m a : ℚ) * number (iZ a) (h_dim a) L := sorry

end Intersection
end AlgebraicGeometry.AlgebraicSpace.Modules
