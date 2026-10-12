/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap42.Lemma_42_47_11_IntersectionProduct
public import stacks_project.Chap42.«42_50_2_1_BivariantPushforward»
public import ReasLib.AlgebraicGeometry.Scheme.Pullback.Square

@[expose] public section

open CategoryTheory CategoryTheory.Limits

noncomputable section

universe u

namespace AlgebraicGeometry.BivariantClass.IteratedIntersection

/-- The degree of an ordered nonempty finite family, accumulated from the last
member toward the first. -/
def degree : {n : ℕ} → (Fin (n + 1) → ℤ) → ℤ
  | 0, p => p 0
  | n + 1, p => p (Fin.last (n + 1)) + degree (fun j ↦ p j.castSucc)

/-- The degree of a singleton family is its unique degree. -/
theorem degree_zero (p : Fin 1 → ℤ) : degree p = p 0 := sorry

/-- The degree of a successor family is the last degree plus the degree of the prefix. -/
theorem degree_succ {n : ℕ} (p : Fin (n + 2) → ℤ) :
    degree p = p (Fin.last (n + 1)) + degree (fun j ↦ p j.castSucc) := sorry

/-- The recursively accumulated degree agrees with the finite sum. -/
theorem degree_eq_sum {n : ℕ} (p : Fin (n + 1) → ℤ) :
    degree p = ∑ j, p j := sorry

/-- An over-object equipped with a map to a fixed target. -/
structure Cone {S : Scheme.{u}} (X : Over S) where
  /-- The intersection object. -/
  obj : Over S
  /-- Its map to the common target. -/
  map : obj ⟶ X

/-- Construct a cone over a target from its object and structural map. -/
def Cone.of {S : Scheme.{u}} {X Y : Over S} (f : Y ⟶ X) : Cone X :=
  { obj := Y, map := f }

/-- `Cone.of` records the supplied structural map. -/
theorem Cone.of_map {S : Scheme.{u}} {X Y : Over S} (f : Y ⟶ X) :
    (Cone.of f).map = f := sorry

/-- Recursion producing an intersection together with its target map. -/
def cone {S : Scheme.{u}} {X : Over S} :
    (n : ℕ) → (Y : Fin (n + 1) → Over S) → (∀ j, Y j ⟶ X) → Cone X
  | 0, Y, f => { obj := Y 0, map := f 0 }
  | n + 1, Y, f =>
      let previous := cone n (fun j ↦ Y j.castSucc) (fun j ↦ f j.castSucc)
      { obj := pullback (f (Fin.last (n + 1))) previous.map
        map := pullback.snd (f (Fin.last (n + 1))) previous.map ≫ previous.map }

/-- The recursively chosen ordered intersection of a nonempty family of
over-objects mapping to a common target. -/
def object {S : Scheme.{u}} {X : Over S} {n : ℕ}
    (Y : Fin (n + 1) → Over S) (f : ∀ j, Y j ⟶ X) : Over S :=
  (cone n Y f).obj

/-- The canonical map from an ordered intersection to its common target. -/
def toTarget {S : Scheme.{u}} {X : Over S} {n : ℕ}
    (Y : Fin (n + 1) → Over S) (f : ∀ j, Y j ⟶ X) : object Y f ⟶ X :=
  (cone n Y f).map

/-- A singleton ordered intersection is its unique member. -/
theorem object_zero {S : Scheme.{u}} {X : Over S}
    (Y : Fin 1 → Over S) (f : ∀ j, Y j ⟶ X) : object Y f = Y 0 := sorry

/-- A successor ordered intersection is the pullback of its last member and prefix. -/
theorem object_succ {S : Scheme.{u}} {X : Over S} {n : ℕ}
    (Y : Fin (n + 2) → Over S) (f : ∀ j, Y j ⟶ X) :
    object Y f =
      pullback (f (Fin.last (n + 1)))
        (toTarget (fun j ↦ Y j.castSucc) (fun j ↦ f j.castSucc)) := sorry

/-- The map from a singleton intersection is the supplied map of its unique member. -/
theorem toTarget_zero {S : Scheme.{u}} {X : Over S}
    (Y : Fin 1 → Over S) (f : ∀ j, Y j ⟶ X) :
    toTarget Y f = f 0 := sorry

/-- The map from a successor intersection is its second projection followed by the
map from the prefix. -/
theorem toTarget_succ {S : Scheme.{u}} {X : Over S} {n : ℕ}
    (Y : Fin (n + 2) → Over S) (f : ∀ j, Y j ⟶ X) :
    toTarget Y f =
      pullback.snd (f (Fin.last (n + 1)))
          (toTarget (fun j ↦ Y j.castSucc) (fun j ↦ f j.castSucc)) ≫
        toTarget (fun j ↦ Y j.castSucc) (fun j ↦ f j.castSucc) := sorry

/-- The two projections defining a successor intersection form a cartesian square
on underlying schemes. -/
theorem object_succ_isPullback {S : Scheme.{u}} {X : Over S} {n : ℕ}
    (Y : Fin (n + 2) → Over S) (f : ∀ j, Y j ⟶ X) :
    IsPullback
      (pullback.fst (f (Fin.last (n + 1)))
        (toTarget (fun j ↦ Y j.castSucc) (fun j ↦ f j.castSucc))).left
      (pullback.snd (f (Fin.last (n + 1)))
        (toTarget (fun j ↦ Y j.castSucc) (fun j ↦ f j.castSucc))).left
      (f (Fin.last (n + 1))).left
      (toTarget (fun j ↦ Y j.castSucc) (fun j ↦ f j.castSucc)).left := sorry

/-- The projection from an ordered intersection to its first member. -/
def toInit {S : Scheme.{u}} {X : Over S} {n : ℕ}
    (Y : Fin (n + 1) → Over S) (f : ∀ j, Y j ⟶ X) : object Y f ⟶ Y 0 :=
  match n, Y, f with
  | 0, _, _ => 𝟙 _
  | n + 1, Y, f =>
      pullback.snd (f (Fin.last (n + 1)))
          (toTarget (fun j ↦ Y j.castSucc) (fun j ↦ f j.castSucc)) ≫
        toInit (fun j ↦ Y j.castSucc) (fun j ↦ f j.castSucc)

/-- On a singleton intersection, `toInit` is the identity. -/
theorem toInit_zero {S : Scheme.{u}} {X : Over S}
    (Y : Fin 1 → Over S) (f : ∀ j, Y j ⟶ X) : toInit Y f = 𝟙 _ := sorry

/-- The projection from an ordered intersection to its last member. -/
def toLast {S : Scheme.{u}} {X : Over S} {n : ℕ}
    (Y : Fin (n + 1) → Over S) (f : ∀ j, Y j ⟶ X) :
    object Y f ⟶ Y (Fin.last n) :=
  match n, Y, f with
  | 0, _, _ => 𝟙 _
  | n + 1, Y, f =>
      pullback.fst (f (Fin.last (n + 1)))
        (toTarget (fun j ↦ Y j.castSucc) (fun j ↦ f j.castSucc))

/-- On a singleton intersection, `toLast` is the identity. -/
theorem toLast_zero {S : Scheme.{u}} {X : Over S}
    (Y : Fin 1 → Over S) (f : ∀ j, Y j ⟶ X) : toLast Y f = 𝟙 _ := sorry

/-- Pointwise closed immersions form a pointwise proper family. -/
instance familyProperOfClosedImmersion {I : Type u} {X Y : I → Scheme.{u}}
    (f : ∀ j, X j ⟶ Y j) [∀ j, IsClosedImmersion (f j)] :
    ∀ j, IsProper (f j) := sorry

/-- A pointwise proper family is pointwise locally of finite type. -/
instance familyLocallyOfFiniteTypeOfProper {I : Type u} {X Y : I → Scheme.{u}}
    (f : ∀ j, X j ⟶ Y j) [∀ j, IsProper (f j)] :
    ∀ j, LocallyOfFiniteType (f j) := sorry

/-- The canonical map of an iterated intersection is locally of finite type when
all family maps are. -/
instance toTargetLocallyOfFiniteType {S : Scheme.{u}} {X : Over S} {n : ℕ}
    (Y : Fin (n + 1) → Over S) (f : ∀ j, Y j ⟶ X)
    [∀ j, LocallyOfFiniteType (f j).left] :
    LocallyOfFiniteType (toTarget Y f).left := sorry

/-- The canonical map of an iterated intersection is proper when all family maps are. -/
instance toTargetProper {S : Scheme.{u}} {X : Over S} {n : ℕ}
    (Y : Fin (n + 1) → Over S) (f : ∀ j, Y j ⟶ X)
    [∀ j, IsProper (f j).left] : IsProper (toTarget Y f).left := sorry

/-- An iterated intersection is locally of finite type over the base when the target
and all family maps are. -/
instance objectLocallyOfFiniteType {S : Scheme.{u}} {X : Over S} {n : ℕ}
    (Y : Fin (n + 1) → Over S) (f : ∀ j, Y j ⟶ X)
    [LocallyOfFiniteType X.hom] [∀ j, IsProper (f j).left] :
    LocallyOfFiniteType (object Y f).hom := sorry

/-- The ordered product of bivariant classes on a recursively chosen nonempty
intersection, with the last class multiplied on the left. -/
def mul {S : Scheme.{u}} [UniversallyCatenary S]
    (delta : S → ℤ) [IsDimensionFunction delta]
    {X : Over S} [LocallyOfFiniteType X.hom] {n : ℕ}
    (Y : Fin (n + 1) → Over S) (f : ∀ j, Y j ⟶ X)
    [hY : ∀ j, LocallyOfFiniteType (Y j).hom]
    [hproper : ∀ j, IsProper (f j).left]
    (p : Fin (n + 1) → ℤ) (c : ∀ j, BivariantClass delta (f j) (p j)) :
    BivariantClass delta (toTarget Y f) (degree p) :=
  match n, Y, f, hY, hproper, p, c with
  | 0, _, _, _, _, _, c => c 0
  | n + 1, Y, f, _, _, p, c =>
      intersectionMul delta
        (f (Fin.last (n + 1)))
        (toTarget (fun j ↦ Y j.castSucc) (fun j ↦ f j.castSucc))
        (pullback.fst (f (Fin.last (n + 1)))
          (toTarget (fun j ↦ Y j.castSucc) (fun j ↦ f j.castSucc)))
        (pullback.snd (f (Fin.last (n + 1)))
          (toTarget (fun j ↦ Y j.castSucc) (fun j ↦ f j.castSucc)))
        (toTarget Y f) (object_succ_isPullback Y f) rfl
        (c (Fin.last (n + 1)))
        (mul delta (fun j ↦ Y j.castSucc) (fun j ↦ f j.castSucc)
          (fun j ↦ p j.castSucc) (fun j ↦ c j.castSucc))

/-- The ordered product of a singleton family is its unique class. -/
theorem mul_zero {S : Scheme.{u}} [UniversallyCatenary S]
    (delta : S → ℤ) [IsDimensionFunction delta]
    {X : Over S} [LocallyOfFiniteType X.hom]
    (Y : Fin 1 → Over S) (f : ∀ j, Y j ⟶ X)
    [∀ j, LocallyOfFiniteType (Y j).hom]
    [∀ j, IsProper (f j).left]
    (p : Fin 1 → ℤ) (c : ∀ j, BivariantClass delta (f j) (p j)) :
    mul delta Y f p c = c 0 := sorry

/-- The ordered product of a successor family multiplies the last class on the left
of the product of the prefix. -/
theorem mul_succ {S : Scheme.{u}} [UniversallyCatenary S]
    (delta : S → ℤ) [IsDimensionFunction delta]
    {X : Over S} [LocallyOfFiniteType X.hom] {n : ℕ}
    (Y : Fin (n + 2) → Over S) (f : ∀ j, Y j ⟶ X)
    [∀ j, LocallyOfFiniteType (Y j).hom]
    [∀ j, IsProper (f j).left]
    (p : Fin (n + 2) → ℤ) (c : ∀ j, BivariantClass delta (f j) (p j)) :
    mul delta Y f p c =
      intersectionMul delta
        (f (Fin.last (n + 1)))
        (toTarget (fun j ↦ Y j.castSucc) (fun j ↦ f j.castSucc))
        (pullback.fst (f (Fin.last (n + 1)))
          (toTarget (fun j ↦ Y j.castSucc) (fun j ↦ f j.castSucc)))
        (pullback.snd (f (Fin.last (n + 1)))
          (toTarget (fun j ↦ Y j.castSucc) (fun j ↦ f j.castSucc)))
        (toTarget Y f) (object_succ_isPullback Y f) rfl
        (c (Fin.last (n + 1)))
        (mul delta (fun j ↦ Y j.castSucc) (fun j ↦ f j.castSucc)
          (fun j ↦ p j.castSucc) (fun j ↦ c j.castSucc)) := sorry

/-- A morphism between cones whose structural maps commute with a specified map
between their targets. -/
structure ConeMap {S : Scheme.{u}} {W X : Over S} (w : W ⟶ X)
    (source : Cone W) (target : Cone X) where
  /-- The map between the cone objects. -/
  map : source.obj ⟶ target.obj
  /-- Compatibility with the structural maps of the two cones. -/
  comm : map ≫ target.map = source.map ≫ w

/-- Construct a map of cones from a map and its compatibility equation. -/
def ConeMap.of {S : Scheme.{u}} {W X : Over S} {w : W ⟶ X}
    {source : Cone W} {target : Cone X} (map : source.obj ⟶ target.obj)
    (comm : map ≫ target.map = source.map ≫ w) : ConeMap w source target :=
  { map := map, comm := comm }

/-- `ConeMap.of` retains the supplied map. -/
theorem ConeMap.of_map {S : Scheme.{u}} {W X : Over S} {w : W ⟶ X}
    {source : Cone W} {target : Cone X} (map : source.obj ⟶ target.obj)
    (comm : map ≫ target.map = source.map ≫ w) :
    (ConeMap.of map comm).map = map := sorry

/-- The second projection of a singleton pullback family commutes with its target maps. -/
theorem baseChange_zero_comm {S : Scheme.{u}} {W X : Over S} (w : W ⟶ X)
    (Y : Fin 1 → Over S) (f : ∀ j, Y j ⟶ X) :
    pullback.snd w (f 0) ≫ f 0 = pullback.fst w (f 0) ≫ w := sorry

/-- The two proposed components of the successor base-change comparison satisfy
the pullback compatibility equation. -/
theorem baseChange_succ_square {S : Scheme.{u}} {W X : Over S} (w : W ⟶ X)
    {n : ℕ} (Y : Fin (n + 2) → Over S) (f : ∀ j, Y j ⟶ X)
    (g : (cone n
        (fun j ↦ pullback w (f j.castSucc))
        (fun j ↦ pullback.fst w (f j.castSucc))).obj ⟶
      (cone n (fun j ↦ Y j.castSucc) (fun j ↦ f j.castSucc)).obj)
    (comm : g ≫ (cone n (fun j ↦ Y j.castSucc) (fun j ↦ f j.castSucc)).map =
      (cone n (fun j ↦ pullback w (f j.castSucc))
        (fun j ↦ pullback.fst w (f j.castSucc))).map ≫ w) :
    (pullback.fst (pullback.fst w (f (Fin.last (n + 1))))
          (cone n (fun j ↦ pullback w (f j.castSucc))
            (fun j ↦ pullback.fst w (f j.castSucc))).map ≫
        pullback.snd w (f (Fin.last (n + 1)))) ≫ f (Fin.last (n + 1)) =
      (pullback.snd (pullback.fst w (f (Fin.last (n + 1))))
          (cone n (fun j ↦ pullback w (f j.castSucc))
            (fun j ↦ pullback.fst w (f j.castSucc))).map ≫ g) ≫
        (cone n (fun j ↦ Y j.castSucc) (fun j ↦ f j.castSucc)).map := sorry

/-- The successor comparison assembled by the pullback universal property commutes
with the maps to the two common targets. -/
theorem baseChange_succ_comm {S : Scheme.{u}} {W X : Over S} (w : W ⟶ X)
    {n : ℕ} (Y : Fin (n + 2) → Over S) (f : ∀ j, Y j ⟶ X)
    (g : (cone n
        (fun j ↦ pullback w (f j.castSucc))
        (fun j ↦ pullback.fst w (f j.castSucc))).obj ⟶
      (cone n (fun j ↦ Y j.castSucc) (fun j ↦ f j.castSucc)).obj)
    (comm : g ≫ (cone n (fun j ↦ Y j.castSucc) (fun j ↦ f j.castSucc)).map =
      (cone n (fun j ↦ pullback w (f j.castSucc))
        (fun j ↦ pullback.fst w (f j.castSucc))).map ≫ w) :
    pullback.lift
          (pullback.fst (pullback.fst w (f (Fin.last (n + 1))))
              (cone n (fun j ↦ pullback w (f j.castSucc))
                (fun j ↦ pullback.fst w (f j.castSucc))).map ≫
            pullback.snd w (f (Fin.last (n + 1))))
          (pullback.snd (pullback.fst w (f (Fin.last (n + 1))))
              (cone n (fun j ↦ pullback w (f j.castSucc))
                (fun j ↦ pullback.fst w (f j.castSucc))).map ≫ g)
          (baseChange_succ_square w Y f g comm) ≫
        (cone (n + 1) Y f).map =
      (cone (n + 1)
          (fun j ↦ pullback w (f j))
          (fun j ↦ pullback.fst w (f j))).map ≫ w := sorry

/-- The canonical comparison from the ordered intersection of the pullbacks of a
family along `w` to the ordered intersection of the original family. -/
def baseChange {S : Scheme.{u}} {W X : Over S} (w : W ⟶ X) :
    (n : ℕ) → (Y : Fin (n + 1) → Over S) → (f : ∀ j, Y j ⟶ X) →
      ConeMap w
        (cone n (fun j ↦ pullback w (f j)) (fun j ↦ pullback.fst w (f j)))
        (cone n Y f)
  | 0, Y, f =>
      { map := pullback.snd w (f 0), comm := baseChange_zero_comm w Y f }
  | n + 1, Y, f =>
      let previousSource :=
        (cone n (fun j ↦ pullback w (f j.castSucc))
          (fun j ↦ pullback.fst w (f j.castSucc))).map
      let previous := baseChange w n (fun j ↦ Y j.castSucc) (fun j ↦ f j.castSucc)
      { map := pullback.lift
          (pullback.fst (pullback.fst w (f (Fin.last (n + 1)))) previousSource ≫
            pullback.snd w (f (Fin.last (n + 1))))
          (pullback.snd (pullback.fst w (f (Fin.last (n + 1)))) previousSource ≫
            previous.map)
          (baseChange_succ_square w Y f previous.map previous.comm)
        comm := baseChange_succ_comm w Y f previous.map previous.comm }

/-- The underlying canonical base-change comparison map between the two ordered
intersections. -/
def baseChangeMap {S : Scheme.{u}} {W X : Over S} (w : W ⟶ X) {n : ℕ}
    (Y : Fin (n + 1) → Over S) (f : ∀ j, Y j ⟶ X) :
    object (fun j ↦ pullback w (f j)) (fun j ↦ pullback.fst w (f j)) ⟶ object Y f :=
  (baseChange w n Y f).map

/-- The base-change comparison factors the source target map through `w`. -/
theorem baseChangeMap_factor {S : Scheme.{u}} {W X : Over S} (w : W ⟶ X) {n : ℕ}
    (Y : Fin (n + 1) → Over S) (f : ∀ j, Y j ⟶ X) :
    toTarget (fun j ↦ pullback w (f j)) (fun j ↦ pullback.fst w (f j)) ≫ w =
      baseChangeMap w Y f ≫ toTarget Y f := sorry

/-- The canonical base-change comparison is proper when the map being pulled back is
proper. -/
instance baseChangeMapProper {S : Scheme.{u}} {W X : Over S} (w : W ⟶ X)
    [IsProper w.left] {n : ℕ} (Y : Fin (n + 1) → Over S) (f : ∀ j, Y j ⟶ X) :
    IsProper (baseChangeMap w Y f).left := sorry

/-- The source of an ordered base-change comparison is locally of finite type over
the base when its common target is and the original family maps are proper. -/
instance baseChangeSourceLocallyOfFiniteType
    {S : Scheme.{u}} {W X : Over S} [LocallyOfFiniteType W.hom]
    (w : W ⟶ X) {n : ℕ} (Y : Fin (n + 1) → Over S) (f : ∀ j, Y j ⟶ X)
    [∀ j, IsProper (f j).left] :
    LocallyOfFiniteType
      (object (fun j ↦ pullback w (f j)) (fun j ↦ pullback.fst w (f j))).hom := sorry

end AlgebraicGeometry.BivariantClass.IteratedIntersection
