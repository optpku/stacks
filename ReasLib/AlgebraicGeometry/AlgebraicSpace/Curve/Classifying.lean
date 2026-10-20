module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Curve.FamilyOver
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Curve.Hom
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.StackInSets.Points
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.SchemeOver
public import ReasLib.CategoryTheory.Fibered.InGroupoids.Cartesian

/-!
# Classification of families of curves

Pullback along scheme-valued points defines the absolute and relative classifying functors
for families of curves over an algebraic space.
-/

@[expose] public section

-- Local declaration justification (metaprogramming implementation): exposed data definitions
-- must reference their private construction and projection laws under Lean's module visibility rules.
set_option backward.privateInPublic true

open CategoryTheory AlgebraicGeometry CategoryTheory.Limits
open AlgebraicGeometry.AlgebraicSpace

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Spaces.Curves

/-- Cartesian functors from the stack of points of an algebraic space to the stack of curves. -/
abbrev Mor {S : Scheme.{u}} (T : AlgebraicSpace S) :=
  CartesianBasedFunctor (stackInSets T).p (p S)

/-- A morphism into the stack of curves commutes strictly with the base projections. -/
theorem mor_w {S : Scheme.{u}} {T : AlgebraicSpace S} (F : Mor T) :
    F.toFunctor ⋙ p S = (stackInSets T).p := F.toBasedFunctor.w

private def classifyingPoint {S : Scheme.{u}} {T : AlgebraicSpace S}
    (P : FamilyOver T) (x : (stackInSets T).total) : Obj S :=
  mk (pullback.snd (FamilyOver.hom P) (stackInSets.pointHom x))

private def classifyingPointMap {S : Scheme.{u}} {T : AlgebraicSpace S}
    (P : FamilyOver T) {x y : (stackInSets T).total} (f : x ⟶ y) :
    space (classifyingPoint P x) ⟶ space (classifyingPoint P y) :=
  pullback.map (FamilyOver.hom P) (stackInSets.pointHom x)
    (FamilyOver.hom P) (stackInSets.pointHom y)
    (𝟙 _) ((ofOverFunctor S).map (stackInSets.pointMap f)) (𝟙 T)
    (by simp) (by simpa only [ofOverFunctor, Category.comp_id] using (stackInSets.pointHom_naturality f).symm)

private theorem classifyingToObj_square {S : Scheme.{u}} {T : AlgebraicSpace S}
    (P : FamilyOver T) {x y : (stackInSets T).total} (f : x ⟶ y) :
    (classifyingPointMap P f ≫ hom (classifyingPoint P y) =
      hom (classifyingPoint P x) ≫ (ofOverFunctor S).map (stackInSets.pointMap f)) ∧
    IsPullback (classifyingPointMap P f) (hom (classifyingPoint P x))
      (hom (classifyingPoint P y)) ((ofOverFunctor S).map (stackInSets.pointMap f)) := sorry

private def classifyingPointHom {S : Scheme.{u}} {T : AlgebraicSpace S}
    (P : FamilyOver T) {x y : (stackInSets T).total} (f : x ⟶ y) :
    classifyingPoint P x ⟶ classifyingPoint P y :=
  homMk (classifyingPointMap P f) (stackInSets.pointMap f)
    (classifyingToObj_square P f).1 (classifyingToObj_square P f).2

private theorem classifyingToObj_laws {S : Scheme.{u}} {T : AlgebraicSpace S}
    (P : FamilyOver T) :
    (∀ x, classifyingPointHom P (𝟙 x) = 𝟙 (classifyingPoint P x)) ∧
    (∀ {x y z : (stackInSets T).total} (f : x ⟶ y) (g : y ⟶ z),
      classifyingPointHom P (f ≫ g) = classifyingPointHom P f ≫ classifyingPointHom P g) :=
  sorry

/-- Pullback of a fixed family along scheme-valued points, as a functor to curve families. -/
def classifyingToObj {S : Scheme.{u}} {T : AlgebraicSpace S} (P : FamilyOver T) :
    (stackInSets T).total ⥤ Obj S where
  obj := classifyingPoint P
  map := classifyingPointHom P
  map_id := (classifyingToObj_laws P).1
  map_comp := (classifyingToObj_laws P).2

/-- Evaluation of the pullback functor is the actual pullback family. -/
theorem classifyingToObj_obj {S : Scheme.{u}} {T : AlgebraicSpace S}
    (P : FamilyOver T) (x : (stackInSets T).total) :
    (classifyingToObj P).obj x =
      mk (pullback.snd (FamilyOver.hom P) (stackInSets.pointHom x)) := rfl

private theorem classifyingToObj_over {S : Scheme.{u}} {T : AlgebraicSpace S}
    (P : FamilyOver T) : classifyingToObj P ⋙ p S = (stackInSets T).p := sorry

/-- The cartesian functor to curves determined by a family over an algebraic space. -/
def classifyingFunctor {S : Scheme.{u}} {T : AlgebraicSpace S}
    (P : FamilyOver T) : Mor T :=
  CartesianBasedFunctor.ofTargetInGroupoids
    (BasedFunctor.ofFunctor (classifyingToObj P) (classifyingToObj_over P))

/-- Forgetting the cartesian structure recovers the pullback functor. -/
theorem classifyingFunctor_toFunctor {S : Scheme.{u}} {T : AlgebraicSpace S}
    (P : FamilyOver T) :
    (classifyingFunctor P).toFunctor = classifyingToObj P := rfl

private def classifyingMapSpace {S : Scheme.{u}} {T : AlgebraicSpace S}
    {P Q : FamilyOver T} (φ : P ⟶ Q) (x : (stackInSets T).total) :
    space (classifyingPoint P x) ⟶ space (classifyingPoint Q x) :=
  pullback.map (FamilyOver.hom P) (stackInSets.pointHom x)
    (FamilyOver.hom Q) (stackInSets.pointHom x)
    (FamilyOver.spaceMap φ) (𝟙 _) (𝟙 T)
    (by simpa only [FamilyOver.hom, FamilyOver.spaceMap, Category.comp_id] using φ.iso.hom.hom.w.symm) (by simp)

private theorem classifyingMap_square {S : Scheme.{u}} {T : AlgebraicSpace S}
    {P Q : FamilyOver T} (φ : P ⟶ Q) (x : (stackInSets T).total) :
    (classifyingMapSpace φ x ≫ hom (classifyingPoint Q x) =
      hom (classifyingPoint P x) ≫ (ofOverFunctor S).map (𝟙 (stackInSets.pointBase x))) ∧
    IsPullback (classifyingMapSpace φ x) (hom (classifyingPoint P x))
      (hom (classifyingPoint Q x)) ((ofOverFunctor S).map (𝟙 (stackInSets.pointBase x))) :=
  sorry

private def classifyingMapApp {S : Scheme.{u}} {T : AlgebraicSpace S}
    {P Q : FamilyOver T} (φ : P ⟶ Q) (x : (stackInSets T).total) :
    (classifyingToObj P).obj x ⟶ (classifyingToObj Q).obj x :=
  homMk (classifyingMapSpace φ x) (𝟙 (stackInSets.pointBase x))
    (classifyingMap_square φ x).1 (classifyingMap_square φ x).2

private theorem classifyingMap_laws {S : Scheme.{u}} {T : AlgebraicSpace S}
    {P Q : FamilyOver T} (φ : P ⟶ Q) :
    (∀ {x y : (stackInSets T).total} (f : x ⟶ y),
      (classifyingToObj P).map f ≫ classifyingMapApp φ y =
        classifyingMapApp φ x ≫ (classifyingToObj Q).map f) ∧
    (∀ x, (p S).IsHomLift (𝟙 ((stackInSets T).p.obj x)) (classifyingMapApp φ x)) := sorry

private def classifyingMap {S : Scheme.{u}} {T : AlgebraicSpace S}
    {P Q : FamilyOver T} (φ : P ⟶ Q) : classifyingFunctor P ⟶ classifyingFunctor Q :=
  CartesianBasedFunctor.homMk
    { app := classifyingMapApp φ
      naturality := fun {_ _} f ↦ (classifyingMap_laws φ).1 f
      isHomLift' := (classifyingMap_laws φ).2 }

private theorem classifying_laws {S : Scheme.{u}} (T : AlgebraicSpace S) :
    (∀ P : FamilyOver T, classifyingMap (𝟙 P) = 𝟙 (classifyingFunctor P)) ∧
    (∀ {P Q R : FamilyOver T} (φ : P ⟶ Q) (ψ : Q ⟶ R),
      classifyingMap (φ ≫ ψ) = classifyingMap φ ≫ classifyingMap ψ) := sorry

/-- The functor classifying families of curves by their scheme-valued pullbacks. -/
def classifying {S : Scheme.{u}} (T : AlgebraicSpace S) : FamilyOver T ⥤ Mor T where
  obj := classifyingFunctor
  map := classifyingMap
  map_id := (classifying_laws T).1
  map_comp := (classifying_laws T).2

/-- Classification sends a family to its cartesian pullback functor. -/
theorem classifying_obj {S : Scheme.{u}} {T : AlgebraicSpace S} (P : FamilyOver T) :
    (classifying T).obj P = classifyingFunctor P := rfl

/-- Classification at a scheme-valued point is the actual pullback family. -/
theorem classifying_obj_point {S : Scheme.{u}} {T : AlgebraicSpace S}
    (P : FamilyOver T) (x : (stackInSets T).total) :
    ((classifying T).obj P).toFunctor.obj x =
      mk (pullback.snd (FamilyOver.hom P) (stackInSets.pointHom x)) := rfl

/-- Scheme-valued points of the domain of a base map, regarded as schemes over its codomain. -/
def pointOver {S : Scheme.{u}} {T B : AlgebraicSpace S} (b : T ⟶ B) :
    (stackInSets T).total ⥤ SchemeOver B where
  obj x := SchemeOver.mk (stackInSets.pointHom x ≫ b)
  map {x y} f := CostructuredArrow.homMk (stackInSets.pointMap f)
    (by change (ofOverFunctor S).map (stackInSets.pointMap f) ≫
          (stackInSets.pointHom y ≫ b) = stackInSets.pointHom x ≫ b
        rw [← Category.assoc, stackInSets.pointHom_naturality]
        rfl)
  map_id x := by apply CostructuredArrow.hom_ext; rfl
  map_comp f g := by apply CostructuredArrow.hom_ext; rfl

/-- Cartesian functors over schemes over the target of a base map into the relative curve stack. -/
abbrev MorOver {S : Scheme.{u}} {T B : AlgebraicSpace S} (b : T ⟶ B) :=
  CartesianBasedFunctor (pointOver b) (CostructuredArrow.pre (p S) (ofOverFunctor S) B)

private def classifyingOverPoint {S : Scheme.{u}} {T B : AlgebraicSpace S}
    (b : T ⟶ B) (P : FamilyOver T) (x : (stackInSets T).total) :
    CostructuredArrow (p S ⋙ ofOverFunctor S) B :=
  CostructuredArrow.mk (Y := (classifyingToObj P).obj x) (stackInSets.pointHom x ≫ b)

private def classifyingOverPointHom {S : Scheme.{u}} {T B : AlgebraicSpace S}
    (b : T ⟶ B) (P : FamilyOver T) {x y : (stackInSets T).total} (f : x ⟶ y) :
    classifyingOverPoint b P x ⟶ classifyingOverPoint b P y :=
  CostructuredArrow.homMk ((classifyingToObj P).map f)
    (by change (ofOverFunctor S).map (stackInSets.pointMap f) ≫
          (stackInSets.pointHom y ≫ b) = stackInSets.pointHom x ≫ b
        rw [← Category.assoc, stackInSets.pointHom_naturality]
        rfl)

private theorem classifyingOverToObj_laws {S : Scheme.{u}} {T B : AlgebraicSpace S}
    (b : T ⟶ B) (P : FamilyOver T) :
    (∀ x, classifyingOverPointHom b P (𝟙 x) = 𝟙 (classifyingOverPoint b P x)) ∧
    (∀ {x y z : (stackInSets T).total} (f : x ⟶ y) (g : y ⟶ z),
      classifyingOverPointHom b P (f ≫ g) =
        classifyingOverPointHom b P f ≫ classifyingOverPointHom b P g) := sorry

private def classifyingOverToObj {S : Scheme.{u}} {T B : AlgebraicSpace S}
    (b : T ⟶ B) (P : FamilyOver T) :
    (stackInSets T).total ⥤ CostructuredArrow (p S ⋙ ofOverFunctor S) B where
  obj := classifyingOverPoint b P
  map := classifyingOverPointHom b P
  map_id := (classifyingOverToObj_laws b P).1
  map_comp := (classifyingOverToObj_laws b P).2

private theorem classifyingOverToObj_over {S : Scheme.{u}} {T B : AlgebraicSpace S}
    (b : T ⟶ B) (P : FamilyOver T) :
    classifyingOverToObj b P ⋙ CostructuredArrow.pre (p S) (ofOverFunctor S) B =
      pointOver b := sorry

private def classifyingOverBased {S : Scheme.{u}} {T B : AlgebraicSpace S}
    (b : T ⟶ B) (P : FamilyOver T) :=
  BasedFunctor.ofFunctor (classifyingOverToObj b P) (classifyingOverToObj_over b P)

private theorem classifyingOverFunctor_cartesian {S : Scheme.{u}} {T B : AlgebraicSpace S}
    (b : T ⟶ B) (P : FamilyOver T) :
    (classifyingOverBased b P).PreservesStronglyCartesian := sorry

private def classifyingOverFunctor {S : Scheme.{u}} {T B : AlgebraicSpace S}
    (b : T ⟶ B) (P : FamilyOver T) : MorOver b :=
  CartesianBasedFunctor.ofBasedFunctor (classifyingOverBased b P)
    (classifyingOverFunctor_cartesian b P)

private def classifyingOverMapApp {S : Scheme.{u}} {T B : AlgebraicSpace S}
    (b : T ⟶ B) {P Q : FamilyOver T} (φ : P ⟶ Q) (x : (stackInSets T).total) :
    (classifyingOverToObj b P).obj x ⟶ (classifyingOverToObj b Q).obj x :=
  CostructuredArrow.homMk (classifyingMapApp φ x)
    (by change (ofOverFunctor S).map (𝟙 (stackInSets.pointBase x)) ≫
          (stackInSets.pointHom x ≫ b) = stackInSets.pointHom x ≫ b
        simp only [ofOverFunctor, CategoryTheory.Functor.map_id, Category.id_comp])

private theorem classifyingOverMap_laws {S : Scheme.{u}} {T B : AlgebraicSpace S}
    (b : T ⟶ B) {P Q : FamilyOver T} (φ : P ⟶ Q) :
    (∀ {x y : (stackInSets T).total} (f : x ⟶ y),
      (classifyingOverToObj b P).map f ≫ classifyingOverMapApp b φ y =
        classifyingOverMapApp b φ x ≫ (classifyingOverToObj b Q).map f) ∧
    (∀ x, (CostructuredArrow.pre (p S) (ofOverFunctor S) B).IsHomLift
      (𝟙 ((pointOver b).obj x)) (classifyingOverMapApp b φ x)) := sorry

private def classifyingOverMap {S : Scheme.{u}} {T B : AlgebraicSpace S}
    (b : T ⟶ B) {P Q : FamilyOver T} (φ : P ⟶ Q) :
    classifyingOverFunctor b P ⟶ classifyingOverFunctor b Q :=
  CartesianBasedFunctor.homMk
    { app := classifyingOverMapApp b φ
      naturality := fun {_ _} f ↦ (classifyingOverMap_laws b φ).1 f
      isHomLift' := (classifyingOverMap_laws b φ).2 }

private theorem classifyingOver_laws {S : Scheme.{u}} {T B : AlgebraicSpace S}
    (b : T ⟶ B) :
    (∀ P : FamilyOver T, classifyingOverMap b (𝟙 P) = 𝟙 (classifyingOverFunctor b P)) ∧
    (∀ {P Q R : FamilyOver T} (φ : P ⟶ Q) (ψ : Q ⟶ R),
      classifyingOverMap b (φ ≫ ψ) = classifyingOverMap b φ ≫ classifyingOverMap b ψ) := sorry

/-- The relative classifying functor carries pullback families and their structural maps to the base. -/
def classifyingOver {S : Scheme.{u}} {T B : AlgebraicSpace S} (b : T ⟶ B) :
    FamilyOver T ⥤ MorOver b where
  obj := classifyingOverFunctor b
  map := classifyingOverMap b
  map_id := (classifyingOver_laws b).1
  map_comp := (classifyingOver_laws b).2

private def forgetBaseToObj {S : Scheme.{u}} {T B : AlgebraicSpace S}
    (b : T ⟶ B) (F : MorOver b) : (stackInSets T).total ⥤ Obj S :=
  F.toFunctor ⋙ CostructuredArrow.proj (p S ⋙ ofOverFunctor S) B

private theorem forgetBaseFunctor_over {S : Scheme.{u}} {T B : AlgebraicSpace S}
    (b : T ⟶ B) (F : MorOver b) :
    forgetBaseToObj b F ⋙ p S = (stackInSets T).p := sorry

private def forgetBaseBased {S : Scheme.{u}} {T B : AlgebraicSpace S}
    (b : T ⟶ B) (F : MorOver b) :=
  BasedFunctor.ofFunctor (forgetBaseToObj b F) (forgetBaseFunctor_over b F)

private theorem forgetBaseFunctor_cartesian {S : Scheme.{u}} {T B : AlgebraicSpace S}
    (b : T ⟶ B) (F : MorOver b) :
    (forgetBaseBased b F).PreservesStronglyCartesian := sorry

private def forgetBaseFunctor {S : Scheme.{u}} {T B : AlgebraicSpace S}
    (b : T ⟶ B) (F : MorOver b) : Mor T :=
  CartesianBasedFunctor.ofBasedFunctor (forgetBaseBased b F)
    (forgetBaseFunctor_cartesian b F)

private def forgetBaseNatTrans {S : Scheme.{u}} {T B : AlgebraicSpace S}
    (b : T ⟶ B) {F G : MorOver b} (η : F ⟶ G) :
    forgetBaseToObj b F ⟶ forgetBaseToObj b G :=
  Functor.whiskerRight η.hom.toNatTrans (CostructuredArrow.proj (p S ⋙ ofOverFunctor S) B)

private theorem forgetBaseMap_laws {S : Scheme.{u}} {T B : AlgebraicSpace S}
    (b : T ⟶ B) {F G : MorOver b} (η : F ⟶ G) :
    ∀ x, (p S).IsHomLift (𝟙 ((stackInSets T).p.obj x))
      ((forgetBaseNatTrans b η).app x) := sorry

private def forgetBaseMap {S : Scheme.{u}} {T B : AlgebraicSpace S}
    (b : T ⟶ B) {F G : MorOver b} (η : F ⟶ G) :
    forgetBaseFunctor b F ⟶ forgetBaseFunctor b G :=
  CartesianBasedFunctor.homMk
    { toNatTrans := forgetBaseNatTrans b η
      isHomLift' := forgetBaseMap_laws b η }

private theorem forgetBase_laws {S : Scheme.{u}} {T B : AlgebraicSpace S} (b : T ⟶ B) :
    (∀ F : MorOver b, forgetBaseMap b (𝟙 F) = 𝟙 (forgetBaseFunctor b F)) ∧
    (∀ {F G H : MorOver b} (η : F ⟶ G) (θ : G ⟶ H),
      forgetBaseMap b (η ≫ θ) = forgetBaseMap b η ≫ forgetBaseMap b θ) := sorry

/-- Forget the structural map to the relative base in a morphism to the relative curve stack. -/
def forgetBase {S : Scheme.{u}} {T B : AlgebraicSpace S} (b : T ⟶ B) : MorOver b ⥤ Mor T where
  obj := forgetBaseFunctor b
  map := forgetBaseMap b
  map_id := (forgetBase_laws b).1
  map_comp := (forgetBase_laws b).2

/-- Forgetting the relative base from the relative classifier recovers absolute classification. -/
theorem classifyingOver_forgetBase {S : Scheme.{u}} {T B : AlgebraicSpace S} (b : T ⟶ B) :
    classifyingOver b ⋙ forgetBase b = classifying T := sorry

/-- Pullback classification identifies families with absolute morphisms to the stack of curves. -/
instance classifying.instIsEquivalence {S : Scheme.{u}} (T : AlgebraicSpace S) :
    (classifying T).IsEquivalence := sorry

/-- Relative and absolute morphisms to the stack of curves form equivalent categories. -/
instance forgetBase.instIsEquivalence {S : Scheme.{u}} {T B : AlgebraicSpace S} (b : T ⟶ B) :
    (forgetBase b).IsEquivalence := sorry

/-- Pullback classification identifies families with relative morphisms to the stack of curves. -/
instance classifyingOver.instIsEquivalence {S : Scheme.{u}} {T B : AlgebraicSpace S}
    (b : T ⟶ B) : (classifyingOver b).IsEquivalence := sorry

/-- For any base map, relative morphisms, absolute morphisms, and families of curves are
identified by the canonical comparison and classification functors. -/
theorem classifying_equivalences {S : Scheme.{u}} {T B : AlgebraicSpace S} (b : T ⟶ B) :
    (forgetBase b).IsEquivalence ∧ (classifying T).IsEquivalence ∧
      (classifyingOver b).IsEquivalence :=
  ⟨inferInstance, inferInstance, inferInstance⟩

end AlgebraicGeometry.AlgebraicSpace.Spaces.Curves
