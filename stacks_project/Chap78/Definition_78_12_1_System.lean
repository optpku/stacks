module

public import stacks_project.Chap78.Definition_78_11_1_Groupoid
public import stacks_project.Chap78.Definition_78_12_1_Pullback

/-!
# Quasi-coherent modules on groupoids in algebraic spaces

A quasi-coherent module on a groupoid in algebraic spaces is a pair `(F, α)`
with `F` quasi-coherent on the object space and `α : t^* F ⟶ s^* F` satisfying
the cocycle law on `R ×_{s, U, t} R` and `e^* α = 𝟙`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Limits

noncomputable section

universe u

namespace AlgebraicGeometry.GroupoidAlgebraicSpace

variable {S : Scheme.{u}} {B : AlgebraicSpace S}

/-- The first projection from the space of composable arrows. -/
def composableFst (G : GroupoidAlgebraicSpace B) :
    (pullback G.s G.t).left ⟶ G.R.left :=
  (pullback.fst G.s G.t).left

/-- The second projection from the space of composable arrows. -/
def composableSnd (G : GroupoidAlgebraicSpace B) :
    (pullback G.s G.t).left ⟶ G.R.left :=
  (pullback.snd G.s G.t).left

/-- The composition map on the underlying algebraic spaces. -/
def compositionMap (G : GroupoidAlgebraicSpace B) :
    (pullback G.s G.t).left ⟶ G.R.left :=
  G.c.left

/-- On composable arrows, the source of the first arrow equals the target of the second. -/
theorem composableConditionLeft (G : GroupoidAlgebraicSpace B) :
    composableFst G ≫ G.s.left = composableSnd G ≫ G.t.left := sorry

/-- The target of a composite is the target of the first arrow. -/
theorem compositionTargetLeft (G : GroupoidAlgebraicSpace B) :
    compositionMap G ≫ G.t.left = composableFst G ≫ G.t.left := sorry

/-- The source of a composite is the source of the second arrow. -/
theorem compositionSourceLeft (G : GroupoidAlgebraicSpace B) :
    compositionMap G ≫ G.s.left = composableSnd G ≫ G.s.left := sorry

/-- The target of an identity arrow is the underlying object. -/
theorem identityTargetLeft (G : GroupoidAlgebraicSpace B) :
    G.e.left ≫ G.t.left = 𝟙 G.U.left := sorry

/-- The source of an identity arrow is the underlying object. -/
theorem identitySourceLeft (G : GroupoidAlgebraicSpace B) :
    G.e.left ≫ G.s.left = 𝟙 G.U.left := sorry

/-- The cocycle condition for an equivariance map `t^* F ⟶ s^* F` on
`R ×_{s, U, t} R`. -/
def Cocycle (G : GroupoidAlgebraicSpace B) (F : AlgebraicSpace.QCoh G.U.left)
    (action : (AlgebraicSpace.QCoh.pullback G.t.left).obj F ⟶
      (AlgebraicSpace.QCoh.pullback G.s.left).obj F) : Prop :=
  reindexAction G.t.left G.s.left (composableFst G) F action ≫
      (pullbackEqIso (composableConditionLeft G)).hom.app F ≫
        reindexAction G.t.left G.s.left (composableSnd G) F action =
    (pullbackEqIso (compositionTargetLeft G)).inv.app F ≫
      reindexAction G.t.left G.s.left (compositionMap G) F action ≫
        (pullbackEqIso (compositionSourceLeft G)).hom.app F

/-- The unit condition `e^* α = 𝟙` after identity comparisons. -/
def Unit (G : GroupoidAlgebraicSpace B) (F : AlgebraicSpace.QCoh G.U.left)
    (action : (AlgebraicSpace.QCoh.pullback G.t.left).obj F ⟶
      (AlgebraicSpace.QCoh.pullback G.s.left).obj F) : Prop :=
  (pullbackIdIso G.U.left).inv.app F ≫
      (pullbackEqIso (identityTargetLeft G)).inv.app F ≫
        reindexAction G.t.left G.s.left G.e.left F action ≫
          (pullbackEqIso (identitySourceLeft G)).hom.app F ≫
            (pullbackIdIso G.U.left).hom.app F =
    𝟙 F

/-- The cocycle law is commutativity of the source square on `R ×_{s, U, t} R`. -/
theorem Cocycle_iff (G : GroupoidAlgebraicSpace B) (F : AlgebraicSpace.QCoh G.U.left)
    (action : (AlgebraicSpace.QCoh.pullback G.t.left).obj F ⟶
      (AlgebraicSpace.QCoh.pullback G.s.left).obj F) :
    Cocycle G F action ↔
      reindexAction G.t.left G.s.left (composableFst G) F action ≫
          (pullbackEqIso (composableConditionLeft G)).hom.app F ≫
            reindexAction G.t.left G.s.left (composableSnd G) F action =
        (pullbackEqIso (compositionTargetLeft G)).inv.app F ≫
          reindexAction G.t.left G.s.left (compositionMap G) F action ≫
            (pullbackEqIso (compositionSourceLeft G)).hom.app F := sorry

/-- The unit law is the identification `e^* α = 𝟙` after identity comparisons. -/
theorem Unit_iff (G : GroupoidAlgebraicSpace B) (F : AlgebraicSpace.QCoh G.U.left)
    (action : (AlgebraicSpace.QCoh.pullback G.t.left).obj F ⟶
      (AlgebraicSpace.QCoh.pullback G.s.left).obj F) :
    Unit G F action ↔
      (pullbackIdIso G.U.left).inv.app F ≫
          (pullbackEqIso (identityTargetLeft G)).inv.app F ≫
            reindexAction G.t.left G.s.left G.e.left F action ≫
              (pullbackEqIso (identitySourceLeft G)).hom.app F ≫
                (pullbackIdIso G.U.left).hom.app F =
        𝟙 F := sorry

/-- A quasi-coherent module on a groupoid in algebraic spaces, with its
equivariance map, cocycle law, and unit law. -/
structure System (G : GroupoidAlgebraicSpace B) where
  /-- The underlying quasi-coherent module on the space of objects. -/
  obj : AlgebraicSpace.QCoh G.U.left
  /-- The equivariance map `t^* F ⟶ s^* F`. -/
  action : (AlgebraicSpace.QCoh.pullback G.t.left).obj obj ⟶
    (AlgebraicSpace.QCoh.pullback G.s.left).obj obj
  /-- The equivariance map satisfies the cocycle condition. -/
  cocycle : Cocycle G obj action
  /-- Pullback of the equivariance map along the identity section is the identity. -/
  unit : Unit G obj action

namespace System

/-- Construct an equivariant quasi-coherent module from its module, action, and laws. -/
def of {G : GroupoidAlgebraicSpace B} (F : AlgebraicSpace.QCoh G.U.left)
    (action : (AlgebraicSpace.QCoh.pullback G.t.left).obj F ⟶
      (AlgebraicSpace.QCoh.pullback G.s.left).obj F)
    (cocycle : Cocycle G F action) (unit : Unit G F action) : System G :=
  ⟨F, action, cocycle, unit⟩

/-- An equivariant quasi-coherent module satisfies its cocycle and unit laws. -/
theorem spec {G : GroupoidAlgebraicSpace B} (A : System G) :
    Cocycle G A.obj A.action ∧ Unit G A.obj A.action := sorry

/-- The constructor recovers the given quasi-coherent module. -/
theorem of_obj {G : GroupoidAlgebraicSpace B} (F : AlgebraicSpace.QCoh G.U.left)
    (action : (AlgebraicSpace.QCoh.pullback G.t.left).obj F ⟶
      (AlgebraicSpace.QCoh.pullback G.s.left).obj F)
    (cocycle : Cocycle G F action) (unit : Unit G F action) :
    (of F action cocycle unit).obj = F := sorry

/-- The constructor recovers the given equivariance map. -/
theorem of_action {G : GroupoidAlgebraicSpace B} (F : AlgebraicSpace.QCoh G.U.left)
    (action : (AlgebraicSpace.QCoh.pullback G.t.left).obj F ⟶
      (AlgebraicSpace.QCoh.pullback G.s.left).obj F)
    (cocycle : Cocycle G F action) (unit : Unit G F action) :
    (of F action cocycle unit).action = action := sorry

end System

end AlgebraicGeometry.GroupoidAlgebraicSpace
