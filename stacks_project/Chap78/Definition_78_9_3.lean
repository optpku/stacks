module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Covering
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Torsor
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry CategoryTheory

universe u

/- Definition 78.9.3 (1): A pseudo `G`-torsor is a principal homogeneous
`G`-space over `B` when it acquires sections on an fpqc covering of `B`. -/
@[stacks 04TY] #check
  (AlgebraicGeometry.GroupAlgebraicSpace.isTorsor_iff :
    ∀ {S : Scheme.{u}} {B : AlgebraicSpace S} (G : GroupAlgebraicSpace B)
      (X : GroupAlgebraicSpace.Action G),
      AlgebraicGeometry.GroupAlgebraicSpace.IsTorsor G X ↔
        Mod.IsPseudoTorsor X ∧
          ∃ U : B.Cover (AlgebraicSpace.fpqcPrecoverage S),
            ∀ i : U.I₀, Nonempty ((Over.mk (U.f i) : Over B) ⟶ X.X))

/- Definition 78.9.3 (2): For `τ` among Zariski, étale, smooth, syntomic, and
fppf, a pseudo `G`-torsor is a `τ` `G`-torsor when it acquires sections on a
`τ`-covering. -/
@[stacks 04TY] #check
  (AlgebraicGeometry.GroupAlgebraicSpace.isStandardTorsor_iff :
    ∀ {S : Scheme.{u}} {B : AlgebraicSpace S} (G : GroupAlgebraicSpace B)
      (X : GroupAlgebraicSpace.Action G) (τ : StandardTopology),
      AlgebraicGeometry.GroupAlgebraicSpace.IsStandardTorsor G X τ ↔
        Mod.IsPseudoTorsor X ∧
          ∃ U : B.Cover (AlgebraicSpace.standardPrecoverage S τ),
            ∀ i : U.I₀, Nonempty ((Over.mk (U.f i) : Over B) ⟶ X.X))

/- Definition 78.9.3 (3): A principal homogeneous `G`-space is quasi-isotrivial
when it is a torsor for the étale topology. -/
@[stacks 04TY] #check
  (AlgebraicGeometry.GroupAlgebraicSpace.isQuasiIsotrivial_iff :
    ∀ {S : Scheme.{u}} {B : AlgebraicSpace S} (G : GroupAlgebraicSpace B)
      (X : GroupAlgebraicSpace.Action G),
      AlgebraicGeometry.GroupAlgebraicSpace.IsQuasiIsotrivial G X ↔
        Mod.IsPseudoTorsor X ∧
          ∃ U : B.Cover (AlgebraicSpace.standardPrecoverage S
              StandardTopology.etale),
            ∀ i : U.I₀, Nonempty ((Over.mk (U.f i) : Over B) ⟶ X.X))

/- Definition 78.9.3 (4): A principal homogeneous `G`-space is locally trivial
when it is a torsor for the Zariski topology. -/
@[stacks 04TY] #check
  (AlgebraicGeometry.GroupAlgebraicSpace.isLocallyTrivial_iff :
    ∀ {S : Scheme.{u}} {B : AlgebraicSpace S} (G : GroupAlgebraicSpace B)
      (X : GroupAlgebraicSpace.Action G),
      AlgebraicGeometry.GroupAlgebraicSpace.IsLocallyTrivial G X ↔
        Mod.IsPseudoTorsor X ∧
          ∃ U : B.Cover (AlgebraicSpace.standardPrecoverage S
              StandardTopology.zariski),
            ∀ i : U.I₀, Nonempty ((Over.mk (U.f i) : Over B) ⟶ X.X))
