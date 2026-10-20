module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Torsor
public import ReasLib.CategoryTheory.Monoidal.Cartesian.PseudoTorsor
public import stacks_project.Chap74.Lemma_74_11_6_Precoverage
public import stacks_project.Chap78.Definition_78_8_1_Action
public import stacks_project.Chap78.Definition_78_9_3_Covering

/-!
# Algebraic-space torsor API

Typed checks retain this import path for the shared mathematical API.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.GroupAlgebraicSpace

variable {S : Scheme.{u}} {B : AlgebraicSpace S} (G : GroupAlgebraicSpace B)
  (X : Action G)

#check (isTrivialOn_iff G X :
  ∀ {K : Precoverage (AlgebraicSpace S)} (U : B.Cover K),
    IsTrivialOn G X U ↔
      ∀ i : U.I₀, Nonempty ((Over.mk (U.f i) : Over B) ⟶ X.X))

#check (isTorsorFor_iff G X :
  ∀ (K : Precoverage (AlgebraicSpace S)),
    IsTorsorFor G X K ↔
      Mod.IsPseudoTorsor X ∧
        ∃ U : B.Cover K,
          ∀ i : U.I₀, Nonempty ((Over.mk (U.f i) : Over B) ⟶ X.X))

#check (IsTorsorFor.mono G X :
  ∀ {K L : Precoverage (AlgebraicSpace S)} (hKL : K ≤ L)
    (hX : IsTorsorFor G X K),
    IsTorsorFor G X L)

#check (isTorsor_iff G X :
  IsTorsor G X ↔
      Mod.IsPseudoTorsor X ∧
        ∃ U : B.Cover (AlgebraicSpace.fpqcPrecoverage S),
          ∀ i : U.I₀, Nonempty ((Over.mk (U.f i) : Over B) ⟶ X.X))

#check (isStandardTorsor_iff G X :
  ∀ (τ : StandardTopology),
    IsStandardTorsor G X τ ↔
      Mod.IsPseudoTorsor X ∧
        ∃ U : B.Cover (AlgebraicSpace.standardPrecoverage S τ),
          ∀ i : U.I₀, Nonempty ((Over.mk (U.f i) : Over B) ⟶ X.X))

#check (isQuasiIsotrivial_iff G X :
  IsQuasiIsotrivial G X ↔
      Mod.IsPseudoTorsor X ∧
        ∃ U : B.Cover (AlgebraicSpace.standardPrecoverage S .etale),
          ∀ i : U.I₀, Nonempty ((Over.mk (U.f i) : Over B) ⟶ X.X))

#check (isLocallyTrivial_iff G X :
  IsLocallyTrivial G X ↔
      Mod.IsPseudoTorsor X ∧
        ∃ U : B.Cover (AlgebraicSpace.standardPrecoverage S .zariski),
          ∀ i : U.I₀, Nonempty ((Over.mk (U.f i) : Over B) ⟶ X.X))

#check (IsStandardTorsor.isTorsor G X :
  ∀ {τ : StandardTopology}
    (hX : IsStandardTorsor G X τ),
    IsTorsor G X)

#check (IsQuasiIsotrivial.isTorsor G X :
  ∀ (hX : IsQuasiIsotrivial G X),
    IsTorsor G X)

#check (IsLocallyTrivial.isTorsor G X :
  ∀ (hX : IsLocallyTrivial G X),
    IsTorsor G X)

end AlgebraicGeometry.GroupAlgebraicSpace
