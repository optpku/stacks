module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.WeaklyAssociatedPoints

/-!
# Weakly associated locus of a module on an algebraic space

The set of weakly associated points of an `𝒪_X`-module, as the points of `|X|`
satisfying the étale-stalk weak-association predicate of Lemma 71.2.1.
-/

open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.Modules

universe u

#check (AlgebraicGeometry.AlgebraicSpace.Modules.weakAss :
  ∀ {S : Scheme.{u}} {X : AlgebraicSpace S} (F : X.Modules), Set (Points X))

#check (AlgebraicGeometry.AlgebraicSpace.Modules.mem_weakAss_iff :
  ∀ {S : Scheme.{u}} {X : AlgebraicSpace S} (F : X.Modules) (x : Points X),
    x ∈ F.weakAss ↔ etaleStalkWeakAss F x)

#check (AlgebraicGeometry.AlgebraicSpace.Modules.mem_weakAss_iff_existsEtaleWeakAss :
  ∀ {S : Scheme.{u}} {X : AlgebraicSpace S} (F : X.Modules) [F.IsQuasicoherent]
    (x : Points X), x ∈ F.weakAss ↔ existsEtaleWeakAss F x)
