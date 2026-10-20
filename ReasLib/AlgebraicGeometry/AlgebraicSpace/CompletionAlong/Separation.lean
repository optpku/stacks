module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.CompletionAlong
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.CompletionAlong.RigSurjective
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.FiniteType
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Noetherian
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Open.Complement
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Separation
public import ReasLib.AlgebraicGeometry.FormalAlgebraicSpace.Separation

/-!
# Separation conditions under completion

Completion along a closed subset preserves quasi-separatedness and separatedness
of morphisms of algebraic spaces. It detects quasi-separatedness for locally
finite-type morphisms to locally Noetherian algebraic spaces that are
isomorphisms over the complementary open. Such a morphism is separated if and
only if its completion map is separated and has rig-surjective relative diagonal.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open CategoryTheory.Limits TopologicalSpace

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- The morphism induced by a quasi-separated morphism of algebraic spaces on
completions along a closed subset and its preimage is quasi-separated. -/
instance quasiSeparated_completionAlongMap {S : Scheme.{u}}
    {X X' : AlgebraicSpace S} (f : X' ⟶ X) [AlgebraicSpace.QuasiSeparated f]
    (T : Closeds (Points X)) :
    FormalAlgebraicSpace.QuasiSeparated (completionAlong.map f T) :=
  sorry

/-- The morphism induced by a separated morphism of algebraic spaces on
completions along a closed subset and its preimage is separated. -/
instance separated_completionAlongMap {S : Scheme.{u}}
    {X X' : AlgebraicSpace S} (f : X' ⟶ X) [AlgebraicSpace.Separated f]
    (T : Closeds (Points X)) :
    FormalAlgebraicSpace.Separated (completionAlong.map f T) :=
  sorry

/-- A locally finite-type morphism to a locally Noetherian algebraic space that
is an isomorphism over the complement of a closed subset is quasi-separated
if and only if its induced morphism of completions is quasi-separated. -/
@[stacks 0ARV]
theorem completionFunctor.quasiSeparated_hom_iff {S : Scheme.{u}}
    {X X' : AlgebraicSpace S} [IsLocallyNoetherian X] (f : X' ⟶ X)
    [LocallyOfFiniteType f] (T : Closeds (Points X))
    [IsIso (openInverseImageTo f (openComplementι X T))] :
    AlgebraicSpace.QuasiSeparated f ↔
      FormalAlgebraicSpace.QuasiSeparated (completionAlong.map f T) :=
  sorry

/-- A locally finite-type morphism to a locally Noetherian algebraic space that
is an isomorphism over the complement of a closed subset is separated if and
only if its induced morphism of completions is separated and its relative
diagonal is rig-surjective. -/
@[stacks 0ARW]
theorem completionFunctor.separated_hom_iff {S : Scheme.{u}}
    {X X' : AlgebraicSpace S} [IsLocallyNoetherian X] (f : X' ⟶ X)
    [LocallyOfFiniteType f] (T : Closeds (Points X))
    [IsIso (openInverseImageTo f (openComplementι X T))] :
    AlgebraicSpace.Separated f ↔
      FormalAlgebraicSpace.Separated (completionAlong.map f T) ∧
        FormalAlgebraicSpace.RigSurjective
          (pullback.diagonal (completionAlong.map f T)) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
