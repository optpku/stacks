/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.AlgebraicGeometry.Fiber
public import Mathlib.AlgebraicGeometry.Stalk
public import ReasLib.AlgebraicGeometry.Scheme.BaseChange.Basic
public import ReasLib.AlgebraicGeometry.Scheme.Etale.Neighborhood
public import ReasLib.AlgebraicGeometry.Scheme.Etale.Neighborhood.Cofiltered
public import ReasLib.AlgebraicGeometry.Scheme.Module.Flat
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.FinitePresentation
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.FiniteType

/-!
# Finite presentation and flatness after an elementary étale refinement

This module records an elementary-étale-local finite-presentation and relative-flatness
neighborhood for a finite-type quasicoherent scheme module.
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Scheme.Modules

/-- After an elementary étale refinement and base change to the spectrum of the selected stalk,
a finite-type quasicoherent module that is flat over the base at a point is finitely presented and
relatively flat on an open neighborhood of the unique point above it. -/
@[stacks 05I5]
theorem exists_elementaryEtale_finitePresentation_flat
    {X S : Scheme.{u}} (f : X ⟶ S) [LocallyOfFinitePresentation f]
    (F : X.Modules) [F.IsQuasicoherent] [F.IsFiniteType]
    (x : X) (h_flat : flatOverAt F f x) :
    ∃ U : EtaleNeighborhood.Elementary S (f x),
      let E := U.obj
      let g := Scheme.fromSpecStalk E.toEtale.left E.point ≫ E.toEtale.hom
      let X' := Limits.pullback f g
      let p := Limits.pullback.snd f g
      let F' := baseChangeModule f g F
      ∃ x' : X',
        (Limits.pullback.fst f g) ⁻¹' {x} = {x'} ∧
          ∃ V : X'.Opens, x' ∈ V ∧
            (F'.restrict V.ι).IsFinitePresentation ∧
              flatOver (F'.restrict V.ι) (V.ι ≫ p) := sorry

/-- After an elementary étale refinement and base change to the spectrum of the selected stalk,
a finite-type quasicoherent module that is flat over the base at a point is relatively flat on an
open neighborhood of the unique point above it. -/
@[stacks 05KT]
theorem existsElementaryEtaleFlatNeighborhoodAt
    {X S : Scheme.{u}} (f : X ⟶ S) [LocallyOfFiniteType f]
    (F : X.Modules) [F.IsQuasicoherent] [F.IsFiniteType]
    (x : X) (h_flat : flatOverAt F f x) :
    ∃ U : EtaleNeighborhood.Elementary S (f x),
      let E := U.obj
      let g := Scheme.fromSpecStalk E.toEtale.left E.point ≫ E.toEtale.hom
      let X' := Limits.pullback f g
      let p := Limits.pullback.snd f g
      let F' := baseChangeModule f g F
      ∃ x' : X',
        (Limits.pullback.fst f g) ⁻¹' {x} = {x'} ∧
          ∃ V : X'.Opens, x' ∈ V ∧
            flatOver (F'.restrict V.ι) (V.ι ≫ p) := sorry

/-- A finite-type quasicoherent module that is fibrewise flat over a finite-presentation morphism
becomes finitely presented and relatively flat on an open containing the entire closed fibre after
an elementary étale refinement and base change to the spectrum of the selected stalk. -/
@[stacks 05KU]
theorem existsElementaryEtaleFlatNeighborhood {X S : Scheme.{u}} (f : X ⟶ S)
    [Scheme.Hom.FinitePresentation f] (F : X.Modules) [F.IsQuasicoherent] [F.IsFiniteType]
    (s : S) (h_flat : ∀ x : f.fiber s, flatOverAt F f (f.fiberι s x)) :
    ∃ U : EtaleNeighborhood.Elementary S s,
      let E := U.obj
      let T := E.toEtale.left
      let g := T.fromSpecStalk E.point ≫ E.toEtale.hom
      let X' := Limits.pullback f g
      let p := Limits.pullback.snd f g
      let F' := baseChangeModule f g F
      let s' := IsLocalRing.closedPoint (T.presheaf.stalk E.point)
      ∃ V : X'.Opens, Set.range (p.fiberι s') ⊆ (V : Set X') ∧
        (F'.restrict V.ι).IsFinitePresentation ∧
          flatOver (F'.restrict V.ι) (V.ι ≫ p) := sorry

/-- A finite-type quasicoherent module that is fibrewise flat over a finite-type morphism becomes
relatively flat on an open containing the entire closed fibre after an elementary étale refinement
and base change to the spectrum of the selected stalk. -/
@[stacks 05KV]
theorem existsElementaryEtaleFlatNeighborhood_of_finiteType {X S : Scheme.{u}} (f : X ⟶ S)
    [Scheme.Hom.FiniteType f] (F : X.Modules) [F.IsQuasicoherent] [F.IsFiniteType]
    (s : S) (h_flat : ∀ x : f.fiber s, flatOverAt F f (f.fiberι s x)) :
    ∃ U : EtaleNeighborhood.Elementary S s,
      let E := U.obj
      let T := E.toEtale.left
      let g := T.fromSpecStalk E.point ≫ E.toEtale.hom
      let X' := Limits.pullback f g
      let p := Limits.pullback.snd f g
      let F' := baseChangeModule f g F
      let s' := IsLocalRing.closedPoint (T.presheaf.stalk E.point)
      ∃ V : X'.Opens, Set.range (p.fiberι s') ⊆ (V : Set X') ∧
        flatOver (F'.restrict V.ι) (V.ι ≫ p) := sorry

end AlgebraicGeometry.Scheme.Modules
