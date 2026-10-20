module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.EtaleSite.Square
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.MeromorphicFunction

/-!
# Pullbacks of meromorphic functions on algebraic spaces

A morphism of algebraic spaces pulls regular structure sections back to regular structure
sections when this holds on every commutative étale square. This is the algebraic-space
analogue of the locally ringed condition that pullbacks of meromorphic functions are defined.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Opposite

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

variable {S : Scheme.{u}}

/-- The structure-sheaf pullback `f♯` on an étale square, as a map of the universe-lifted
rings of sections `𝒪_Y(V) ⟶ 𝒪_X(U)`. -/
abbrev pullbackStructureSection {X Y : AlgebraicSpace S} {f : X ⟶ Y} (sq : EtaleSquare f) :
    (commStructureSheafLift Y).obj.obj (op sq.right) ⟶
      (commStructureSheafLift X).obj.obj (op sq.left) :=
  CommRingCat.liftedMap.{u, u + 1} sq.map.left.appTop

/-- `pullbackStructureSection` is the universe lift of the scheme-level map `appTop`. -/
theorem pullbackStructureSection_eq {X Y : AlgebraicSpace S} {f : X ⟶ Y}
    (sq : EtaleSquare f) :
    pullbackStructureSection sq =
      CommRingCat.liftedMap.{u, u + 1} sq.map.left.appTop :=
  sorry

/-- Applying `pullbackStructureSection` is applying the universe-lifted `appTop`. -/
theorem pullbackStructureSection_apply {X Y : AlgebraicSpace S} {f : X ⟶ Y}
    (sq : EtaleSquare f) (s : (commStructureSheafLift Y).obj.obj (op sq.right)) :
    CommRingCat.Hom.hom (pullbackStructureSection sq) s =
      CommRingCat.Hom.hom (CommRingCat.liftedMap.{u, u + 1} sq.map.left.appTop) s :=
  sorry

/-- Pullbacks of meromorphic functions are defined for `f : X ⟶ Y` when every regular
section in `S_Y(V)` pulls back along `f♯` to a regular section in `S_X(U)`, for every
commutative étale square over `f`. -/
class PullbacksMeromorphicFunctionsDefined {X Y : AlgebraicSpace S} (f : X ⟶ Y) : Prop where
  /-- Regular structure sections are stable under `f♯` on every étale square. -/
  pullback_mem_regularStructureSections :
    ∀ (sq : EtaleSquare f) (s : (commStructureSheafLift Y).obj.obj (op sq.right)),
      s ∈ (regularStructureSections Y).obj (op sq.right) →
        CommRingCat.Hom.hom (pullbackStructureSection sq) s ∈
          (regularStructureSections X).obj (op sq.left)

/-- Pullbacks of meromorphic functions are defined exactly when `f♯` preserves the
multiplicative sets `S_Y(V)` of regular sections on every étale square. -/
theorem pullbacksMeromorphicFunctionsDefined_iff {X Y : AlgebraicSpace S} (f : X ⟶ Y) :
    PullbacksMeromorphicFunctionsDefined f ↔
      ∀ (sq : EtaleSquare f) (s : (commStructureSheafLift Y).obj.obj (op sq.right)),
        s ∈ (regularStructureSections Y).obj (op sq.right) →
          CommRingCat.Hom.hom (pullbackStructureSection sq) s ∈
            (regularStructureSections X).obj (op sq.left) :=
  sorry

/-- On a morphism for which pullbacks of meromorphic functions are defined, `f♯` sends
regular sections on `V` to regular sections on `U`. -/
theorem pullbackStructureSection_mem {X Y : AlgebraicSpace S} {f : X ⟶ Y}
    [PullbacksMeromorphicFunctionsDefined f] (sq : EtaleSquare f)
    {s : (commStructureSheafLift Y).obj.obj (op sq.right)}
    (hs : s ∈ (regularStructureSections Y).obj (op sq.right)) :
    CommRingCat.Hom.hom (pullbackStructureSection sq) s ∈
      (regularStructureSections X).obj (op sq.left) :=
  sorry

/-- A scheme map `g : U ⟶ V` in a commuting square over a morphism for which meromorphic
pullbacks are defined sends regular sections on `V` to regular sections on `U`. -/
theorem pullbackStructureSection_mem_ofSchemeMap {X Y : AlgebraicSpace S} {f : X ⟶ Y}
    [PullbacksMeromorphicFunctionsDefined f] (U : smallEtaleSite X) (V : smallEtaleSite Y)
    (g : U.left ⟶ V.left) (w : U.hom ≫ f = ofOverMap g ≫ V.hom)
    {s : (commStructureSheafLift Y).obj.obj (op V)}
    (hs : s ∈ (regularStructureSections Y).obj (op V)) :
    CommRingCat.Hom.hom (pullbackStructureSection (EtaleSquare.ofSchemeMap U V g w)) s ∈
      (regularStructureSections X).obj (op U) :=
  sorry

/-- Pullbacks of meromorphic functions are defined for the identity morphism of an
algebraic space. -/
instance instPullbacksMeromorphicFunctionsDefined_id {X : AlgebraicSpace S} :
    PullbacksMeromorphicFunctionsDefined (𝟙 X) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
