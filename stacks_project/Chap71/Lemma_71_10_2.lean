module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.MeromorphicFunction.Affine
import StacksCheckRecall

/-!
# Lemma 71.10.2

On an affine scheme étale over an algebraic space `X`, the regular-section
submonoid `S_X(U)` is the set of nonzerodivisors of `𝒪_X(U)`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace Opposite
open scoped AlgebraicGeometry

universe u

/- Lemma 71.10.2: for a scheme `S` and an algebraic space `X` over `S`, if `U` is affine
and étale over `X`, then `(regularStructureSections X).obj (op U.obj)` is the set of
nonzerodivisors of `(commStructureSheafLift X).obj.obj (op U.obj)`. -/
@[stacks 0EN4]
#check (AlgebraicGeometry.AlgebraicSpace.regularStructureSections_eq_nonZeroDivisors :
    ∀ {S : Scheme.{u}} {X : AlgebraicSpace S} (U : affineEtaleSite X),
    (regularStructureSections X).obj (op U.obj) =
      nonZeroDivisors ((commStructureSheafLift X).obj.obj (op U.obj)))

#check (AlgebraicGeometry.AlgebraicSpace.mem_regularStructureSections_iff_mem_nonZeroDivisors :
    ∀ {S : Scheme.{u}} {X : AlgebraicSpace S} {U : affineEtaleSite X}
      (s : (commStructureSheafLift X).obj.obj (op U.obj)),
    s ∈ (regularStructureSections X).obj (op U.obj) ↔
      s ∈ nonZeroDivisors ((commStructureSheafLift X).obj.obj (op U.obj)))

#check (AlgebraicGeometry.AlgebraicSpace.mem_regularStructureSections_iff_down_mem_nonZeroDivisors :
    ∀ {S : Scheme.{u}} {X : AlgebraicSpace S} {U : affineEtaleSite X}
      (s : (commStructureSheafLift X).obj.obj (op U.obj)),
    s ∈ (regularStructureSections X).obj (op U.obj) ↔
      s.down ∈ nonZeroDivisors Γ((smallEtaleToScheme X).obj U.obj, ⊤))

#check (AlgebraicGeometry.AlgebraicSpace.isRegularEtaleSection_iff_mem_nonZeroDivisors :
    ∀ {S : Scheme.{u}} {X : AlgebraicSpace S} {U : affineEtaleSite X}
      (s : (commStructureSheafLift X).obj.obj (op U.obj)),
    IsRegularEtaleSection s ↔
      s ∈ nonZeroDivisors ((commStructureSheafLift X).obj.obj (op U.obj)))
