/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Cohomology.Torsion
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry CategoryTheory
open AlgebraicGeometry.Scheme.Hom

universe u

/- 54.8.2.1: For a normal modification over a two-dimensional local normal Nagata domain,
sections of the zero scheme cut out by a nonzero `a`, modulo constants, identify with
the `a`-torsion submodule of `H¹(X, 𝒪_X)`. -/
@[stacks 0AXK] #check (AlgebraicGeometry.Scheme.Hom.PrincipalZero.cokernelEquivH1Torsion :
  ∀ {A : Type u} [CommRing A] {X : Scheme.{u}}
    [IsLocalRing A] [NagataRing A] [_root_.IsNormalRing A]
    (f : X ⟶ Spec (.of A)) [IsModification f] (a : A)
    (h_dimension : ringKrullDim A = 2) (ha : a ≠ 0) (hX : X.isNormal),
    (PrincipalZero.sections f a ⧸ (PrincipalZero.constants f a).range) ≃ₗ[A]
      Submodule.torsionBy A
        (cohomology f (SheafOfModules.unit X.ringCatSheaf : X.Modules) 1) a)
