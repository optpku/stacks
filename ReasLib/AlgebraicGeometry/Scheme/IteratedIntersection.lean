module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Proper.Over
public import ReasLib.AlgebraicGeometry.Scheme.Over.ClosedImmersion
public import ReasLib.AlgebraicGeometry.Scheme.Pullback.Square

@[expose] public section

open CategoryTheory CategoryTheory.Limits

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.IteratedIntersection

/-- Recursion producing an intersection together with its target map. -/
def cone {S : Scheme.{u}} {X : Over S} :
    (n : ℕ) → (Y : Fin (n + 1) → Over S) → (∀ j, Y j ⟶ X) → Over X
  | 0, Y, f => Over.mk (f 0)
  | n + 1, Y, f =>
      let previous := cone n (fun j ↦ Y j.castSucc) (fun j ↦ f j.castSucc)
      Over.mk (pullback.snd (f (Fin.last (n + 1))) previous.hom ≫ previous.hom)

/-- The recursively chosen ordered intersection of a nonempty family of
over-objects mapping to a common target. -/
def object {S : Scheme.{u}} {X : Over S} {n : ℕ}
    (Y : Fin (n + 1) → Over S) (f : ∀ j, Y j ⟶ X) : Over S :=
  (cone n Y f).left

/-- The canonical map from an ordered intersection to its common target. -/
def toTarget {S : Scheme.{u}} {X : Over S} {n : ℕ}
    (Y : Fin (n + 1) → Over S) (f : ∀ j, Y j ⟶ X) : object Y f ⟶ X :=
  (cone n Y f).hom

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

/-- The second projection of a singleton pullback family commutes with its target maps. -/
private theorem baseChange_zero_comm {S : Scheme.{u}} {W X : Over S} (w : W ⟶ X)
    (Y : Fin 1 → Over S) (f : ∀ j, Y j ⟶ X) :
    pullback.snd w (f 0) ≫ f 0 = pullback.fst w (f 0) ≫ w := sorry

/-- The two proposed components of the successor base-change comparison satisfy
the pullback compatibility equation. -/
private theorem baseChange_succ_square {S : Scheme.{u}} {W X : Over S} (w : W ⟶ X)
    {n : ℕ} (Y : Fin (n + 2) → Over S) (f : ∀ j, Y j ⟶ X)
    (g : (cone n
        (fun j ↦ pullback w (f j.castSucc))
        (fun j ↦ pullback.fst w (f j.castSucc))).left ⟶
      (cone n (fun j ↦ Y j.castSucc) (fun j ↦ f j.castSucc)).left)
    (comm : g ≫ (cone n (fun j ↦ Y j.castSucc) (fun j ↦ f j.castSucc)).hom =
      (cone n (fun j ↦ pullback w (f j.castSucc))
        (fun j ↦ pullback.fst w (f j.castSucc))).hom ≫ w) :
    (pullback.fst (pullback.fst w (f (Fin.last (n + 1))))
          (cone n (fun j ↦ pullback w (f j.castSucc))
            (fun j ↦ pullback.fst w (f j.castSucc))).hom ≫
        pullback.snd w (f (Fin.last (n + 1)))) ≫ f (Fin.last (n + 1)) =
      (pullback.snd (pullback.fst w (f (Fin.last (n + 1))))
          (cone n (fun j ↦ pullback w (f j.castSucc))
            (fun j ↦ pullback.fst w (f j.castSucc))).hom ≫ g) ≫
        (cone n (fun j ↦ Y j.castSucc) (fun j ↦ f j.castSucc)).hom := sorry

/-- The successor comparison assembled by the pullback universal property commutes
with the maps to the two common targets. -/
private theorem baseChange_succ_comm {S : Scheme.{u}} {W X : Over S} (w : W ⟶ X)
    {n : ℕ} (Y : Fin (n + 2) → Over S) (f : ∀ j, Y j ⟶ X)
    (g : (cone n
        (fun j ↦ pullback w (f j.castSucc))
        (fun j ↦ pullback.fst w (f j.castSucc))).left ⟶
      (cone n (fun j ↦ Y j.castSucc) (fun j ↦ f j.castSucc)).left)
    (comm : g ≫ (cone n (fun j ↦ Y j.castSucc) (fun j ↦ f j.castSucc)).hom =
      (cone n (fun j ↦ pullback w (f j.castSucc))
        (fun j ↦ pullback.fst w (f j.castSucc))).hom ≫ w) :
    pullback.lift
          (pullback.fst (pullback.fst w (f (Fin.last (n + 1))))
              (cone n (fun j ↦ pullback w (f j.castSucc))
                (fun j ↦ pullback.fst w (f j.castSucc))).hom ≫
            pullback.snd w (f (Fin.last (n + 1))))
          (pullback.snd (pullback.fst w (f (Fin.last (n + 1))))
              (cone n (fun j ↦ pullback w (f j.castSucc))
                (fun j ↦ pullback.fst w (f j.castSucc))).hom ≫ g)
          (baseChange_succ_square w Y f g comm) ≫
        (cone (n + 1) Y f).hom =
      (cone (n + 1)
          (fun j ↦ pullback w (f j))
          (fun j ↦ pullback.fst w (f j))).hom ≫ w := sorry

/-- The canonical comparison from the ordered intersection of the pullbacks of a
family along `w` to the ordered intersection of the original family. -/
def baseChange {S : Scheme.{u}} {W X : Over S} (w : W ⟶ X) :
    (n : ℕ) → (Y : Fin (n + 1) → Over S) → (f : ∀ j, Y j ⟶ X) →
      (Over.map w).obj
        (cone n (fun j ↦ pullback w (f j)) (fun j ↦ pullback.fst w (f j))) ⟶
        cone n Y f
  | 0, Y, f =>
      Over.homMk (pullback.snd w (f 0)) (by exact baseChange_zero_comm w Y f)
  | n + 1, Y, f =>
      let previousSource :=
        (cone n (fun j ↦ pullback w (f j.castSucc))
          (fun j ↦ pullback.fst w (f j.castSucc))).hom
      let previous := baseChange w n (fun j ↦ Y j.castSucc) (fun j ↦ f j.castSucc)
      Over.homMk (pullback.lift
          (pullback.fst (pullback.fst w (f (Fin.last (n + 1)))) previousSource ≫
            pullback.snd w (f (Fin.last (n + 1))))
          (pullback.snd (pullback.fst w (f (Fin.last (n + 1)))) previousSource ≫
            previous.left)
          (by exact baseChange_succ_square w Y f previous.left (Over.w previous)))
        (by exact baseChange_succ_comm w Y f previous.left (Over.w previous))

/-- The underlying canonical base-change comparison map between the two ordered
intersections. -/
def baseChangeMap {S : Scheme.{u}} {W X : Over S} (w : W ⟶ X) {n : ℕ}
    (Y : Fin (n + 1) → Over S) (f : ∀ j, Y j ⟶ X) :
    object (fun j ↦ pullback w (f j)) (fun j ↦ pullback.fst w (f j)) ⟶ object Y f :=
  (baseChange w n Y f).left

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

/-- The maps from a finite family of closed subschemes to their common ambient
over-object form a pointwise proper family. -/
instance closedFamilyProper
    {S : Scheme.{u}} {X : Over S} {n : ℕ}
    (Z : Fin (n + 1) → Scheme.{u}) (i : ∀ j, Z j ⟶ X.left)
    [∀ j, IsClosedImmersion (i j)] :
    ∀ j, IsProper
      (Over.homMk (i j) : Over.mk (i j ≫ X.hom) ⟶ X).left := sorry

/-- A finite family of closed subschemes of a locally finite-type `S`-scheme is
pointwise locally of finite type over `S`. -/
instance closedFamilyLocallyOfFiniteType
    {S : Scheme.{u}} {X : Over S} [LocallyOfFiniteType X.hom] {n : ℕ}
    (Z : Fin (n + 1) → Scheme.{u}) (i : ∀ j, Z j ⟶ X.left)
    [∀ j, IsClosedImmersion (i j)] :
    ∀ j, LocallyOfFiniteType (Over.mk (i j ≫ X.hom)).hom := sorry

/-- The projections of a closed family pulled back along a morphism over the base
form a pointwise proper family. -/
instance pullbackClosedFamilyProper
    {S : Scheme.{u}} {A X : Over S} (w : A ⟶ X)
    {n : ℕ} (Z : Fin (n + 1) → Scheme.{u}) (i : ∀ j, Z j ⟶ X.left)
    [∀ j, IsClosedImmersion (i j)] :
    ∀ j, IsProper
      (pullback.fst w
        (Over.homMk (i j) : Over.mk (i j ≫ X.hom) ⟶ X)).left := sorry

/-- A closed family pulled back to an object locally of finite type over the base
is pointwise locally of finite type over the base. -/
instance pullbackClosedFamilyLocallyOfFiniteType
    {S : Scheme.{u}} {A X : Over S} [LocallyOfFiniteType A.hom] (w : A ⟶ X)
    {n : ℕ} (Z : Fin (n + 1) → Scheme.{u}) (i : ∀ j, Z j ⟶ X.left)
    [∀ j, IsClosedImmersion (i j)] :
    ∀ j, LocallyOfFiniteType
      (pullback w (Over.homMk (i j) : Over.mk (i j ≫ X.hom) ⟶ X)).hom := sorry

end AlgebraicGeometry.Scheme.IteratedIntersection
