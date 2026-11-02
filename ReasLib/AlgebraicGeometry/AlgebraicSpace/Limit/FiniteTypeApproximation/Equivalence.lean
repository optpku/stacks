/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Limit.FiniteTypeApproximation
public import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
public import Mathlib.CategoryTheory.Equivalence
public import Mathlib.CategoryTheory.Filtered.Final
public import Mathlib.Order.Directed

/-!
# The category of finite-type approximation systems

Comparison morphisms on common tails, modulo eventual equality, form a category.
Its limit functor takes values in quasi-separated finite-type spaces over the base limit.
-/

@[expose] public section

open CategoryTheory Limits

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.FiniteTypeApproximation

variable {I : Type u} [Preorder I] {S : Scheme.{u}}
variable (D : OrderDual I ⥤ AlgebraicSpace S) (c : Cone D)

/-- An admissible approximation system with its chosen limiting cone and good diagram. -/
structure Obj where
  /-- The initial stage. -/
  initial : I
  /-- The inverse system on the initial tail. -/
  diagram : Over (OrderDual.toDual initial) ⥤ AlgebraicSpace S
  /-- The cone with the chosen limiting space as vertex. -/
  cone : Cone diagram
  /-- The structural morphism of the limiting space. -/
  toS : cone.pt ⟶ c.pt
  /-- The structural morphism is quasi-separated. -/
  quasiSeparated : QuasiSeparated toS
  /-- The structural morphism is of finite type. -/
  finiteType : FiniteType toS
  /-- The system arises by scheme-theoretic images from a good diagram. -/
  approximation : FiniteTypeApproximationLimitSystem D c initial diagram cone toS

variable {D c}

/-- The limiting space as an object over the base limit. -/
def Obj.limitObject (X : Obj D c) : Over c.pt := Over.mk X.toS

/-- The structural transformation of an approximation system to its base tail. -/
def Obj.toBase (X : Obj D c) : X.diagram ⟶ tailBaseDiagram D X.initial :=
  X.approximation.toBase

/-- The cone projections commute with the structural morphism to the base limit. -/
theorem Obj.cone_toBase (X : Obj D c) (j : Over (OrderDual.toDual X.initial)) :
    X.cone.π.app j ≫ X.toBase.app j = X.toS ≫ c.π.app j.left :=
  X.approximation.cone_toBase j

/-- A comparison on a common tail together with its compatible morphism of limits. -/
structure Representative (X Y : Obj D c) where
  /-- The starting stage of the common tail. -/
  stage : I
  /-- The common tail lies in the source tail. -/
  source_le : X.initial ≤ stage
  /-- The common tail lies in the target tail. -/
  target_le : Y.initial ≤ stage
  /-- The comparison of the restricted inverse systems over the base. -/
  comparison : InverseSystemMorphismOverBase D stage
    (restrictTail source_le X.diagram) (restrictTail target_le Y.diagram)
    (restrictTailToBase D source_le X.toBase) (restrictTailToBase D target_le Y.toBase)
  /-- The actual morphism of limiting spaces over the base limit. -/
  map : X.limitObject ⟶ Y.limitObject
  /-- The comparison induces the recorded morphism of limits. -/
  compatible : comparison.IsLimitMorphism
    (Cone.whisker (Over.map (homOfLE source_le : OrderDual.toDual stage ⟶ OrderDual.toDual X.initial)) X.cone)
    (Cone.whisker (Over.map (homOfLE target_le : OrderDual.toDual stage ⟶ OrderDual.toDual Y.initial)) Y.cone) map.left

namespace Representative

variable {X Y Z W : Obj D c}

/-- The morphism of limits recorded by a common-tail comparison. -/
def limitHom (f : Representative X Y) : X.limitObject ⟶ Y.limitObject := f.map

/-- The identity comparison starts on the original tail and induces the identity limit map. -/
def id (X : Obj D c) : Representative X X where
  stage := X.initial
  source_le := le_rfl
  target_le := le_rfl
  comparison := InverseSystemMorphismOverBase.id
  map := 𝟙 X.limitObject
  compatible := by
    intro j
    change (𝟙 X.cone.pt) ≫ X.cone.π.app _ = X.cone.π.app _ ≫ 𝟙 _
    simp only [Category.id_comp, Category.comp_id]

variable [directed : IsDirected I (· ≤ ·)]

include directed

/-- Compose comparisons by restricting both to a common later tail. -/
def comp (f : Representative X Y) (g : Representative Y Z) : Representative X Z := by
  let k := Classical.choose (exists_ge_ge f.stage g.stage)
  have hf : f.stage ≤ k := (Classical.choose_spec (exists_ge_ge f.stage g.stage)).1
  have hg : g.stage ≤ k := (Classical.choose_spec (exists_ge_ge f.stage g.stage)).2
  let F := Over.map (homOfLE hf : OrderDual.toDual k ⟶ OrderDual.toDual f.stage)
  let G := Over.map (homOfLE hg : OrderDual.toDual k ⟶ OrderDual.toDual g.stage)
  refine {
    stage := k
    source_le := le_trans f.source_le hf
    target_le := le_trans g.target_le hg
    comparison := Over.homMk
      (Functor.whiskerLeft F f.comparison.hom ≫ Functor.whiskerLeft G g.comparison.hom) ?_
    map := f.map ≫ g.map
    compatible := ?_
  }
  · ext j
    have hff := congrArg (fun η => η.app (F.obj j)) f.comparison.w
    have hgg := congrArg (fun η => η.app (G.obj j)) g.comparison.w
    change (f.comparison.hom.app (F.obj j) ≫ g.comparison.hom.app (G.obj j)) ≫ _ = _
    erw [Category.assoc]
    erw [show g.comparison.hom.app (G.obj j) ≫ _ = _ from hgg]
    exact hff
  · intro j
    change (f.map.left ≫ g.map.left) ≫ _ = _ ≫
      (f.comparison.hom.app (F.obj j) ≫ g.comparison.hom.app (G.obj j))
    erw [Category.assoc, g.compatible (G.obj j), ← Category.assoc,
      f.compatible (F.obj j), Category.assoc]

/-- Two comparisons are equal when their components agree at every sufficiently late stage. -/
def EventuallyEq (f g : Representative X Y) : Prop :=
  ∃ (k : I) (hf : f.stage ≤ k) (hg : g.stage ≤ k),
    ∀ (j : I) (hkj : k ≤ j),
      f.comparison.hom.app (tailObject j (le_trans hf hkj)) =
        g.comparison.hom.app (tailObject j (le_trans hg hkj))

/-- Eventual equality of comparisons is an equivalence relation. -/
theorem eventuallyEq_equivalence : Equivalence (EventuallyEq (X := X) (Y := Y)) := by
  refine ⟨?_, ?_, ?_⟩
  · intro f
    exact ⟨f.stage, le_rfl, le_rfl, fun _ _ => rfl⟩
  · rintro f g ⟨k, hf, hg, h⟩
    exact ⟨k, hg, hf, fun j hj => (h j hj).symm⟩
  · rintro f g h ⟨k, hf, hg, hfg⟩ ⟨l, hg', hh, hgh⟩
    obtain ⟨m, hkm, hlm⟩ := exists_ge_ge k l
    refine ⟨m, le_trans hf hkm, le_trans hh hlm, ?_⟩
    intro j hmj
    exact (hfg j (le_trans hkm hmj)).trans (hgh j (le_trans hlm hmj))

/-- Eventually equal comparisons induce equal morphisms of limits. -/
theorem limitHom_eq_of_eventuallyEq {f g : Representative X Y} (h : EventuallyEq f g) :
    f.limitHom = g.limitHom := by
  obtain ⟨k, hf, hg, hfg⟩ := h
  apply Over.OverMorphism.ext
  apply Y.approximation.isLimit.hom_ext
  intro a
  obtain ⟨j, hkj, haj⟩ := exists_ge_ge k (OrderDual.ofDual a.left)
  let b := tailObject j (le_trans f.target_le (le_trans hf hkj))
  let p : b ⟶ a := Over.homMk (homOfLE haj)
  have hπ := Y.cone.w p
  have he : f.map.left ≫ Y.cone.π.app b = g.map.left ≫ Y.cone.π.app b := by
    erw [f.compatible (tailObject j (le_trans hf hkj)),
      g.compatible (tailObject j (le_trans hg hkj)), hfg j hkj]
    rfl
  change f.map.left ≫ Y.cone.π.app a = g.map.left ≫ Y.cone.π.app a
  erw [← hπ, ← Category.assoc, ← Category.assoc, he]

/-- Composition respects eventual equality in both arguments. -/
theorem comp_congr {f f' : Representative X Y} {g g' : Representative Y Z}
    (hf : EventuallyEq f f') (hg : EventuallyEq g g') :
    EventuallyEq (comp f g) (comp f' g') := by
  obtain ⟨a, hfa, hf'a, ha⟩ := hf
  obtain ⟨b, hgb, hg'b, hb⟩ := hg
  obtain ⟨k, hk, hk'⟩ := exists_ge_ge (comp f g).stage (comp f' g').stage
  obtain ⟨l, hal, hbl⟩ := exists_ge_ge a b
  obtain ⟨m, hkm, hlm⟩ := exists_ge_ge k l
  refine ⟨m, le_trans hk hkm, le_trans hk' hkm, ?_⟩
  intro j hmj
  exact congrArg₂ (fun a b => a ≫ b) (ha j (le_trans hal (le_trans hlm hmj)))
    (hb j (le_trans hbl (le_trans hlm hmj)))

end Representative

/-- Morphisms of approximation systems are common-tail comparisons modulo eventual equality. -/
def Hom (X Y : Obj D c) := Quot (Representative.EventuallyEq (X := X) (Y := Y))

namespace Hom

variable {X Y Z W : Obj D c}

/-- The germ of a common-tail comparison. -/
def mk (f : Representative X Y) : Hom X Y := Quot.mk _ f

variable [directed : IsDirected I (· ≤ ·)]

include directed

/-- The morphism of limits induced by a comparison germ. -/
def limitHom (f : Hom X Y) : X.limitObject ⟶ Y.limitObject :=
  Quot.lift Representative.limitHom
    (fun _ _ h => Representative.limitHom_eq_of_eventuallyEq h) f

/-- The identity comparison germ. -/
def id (X : Obj D c) : Hom X X := mk (Representative.id X)

/-- Composition of comparison germs. -/
def comp (f : Hom X Y) (g : Hom Y Z) : Hom X Z :=
  Quot.liftOn₂ f g (fun a b => mk (Representative.comp a b))
    (fun a _ _ h => Quot.sound
      (Representative.comp_congr (Representative.eventuallyEq_equivalence.refl a) h))
    (fun _ _ b h => Quot.sound
      (Representative.comp_congr h (Representative.eventuallyEq_equivalence.refl b)))

/-- Two representatives have equal germs precisely when they are eventually equal. -/
theorem mk_eq_iff (f g : Representative X Y) : mk f = mk g ↔ f.EventuallyEq g := by
  exact Representative.eventuallyEq_equivalence.quot_mk_eq_iff f g

/-- Passing a representative to its germ preserves its recorded limit map. -/
theorem limitHom_mk (f : Representative X Y) : limitHom (mk f) = f.limitHom := rfl

/-- The identity germ is a left identity for composition. -/
theorem id_comp (f : Hom X Y) : comp (id X) f = f := by
  induction f using Quot.inductionOn with | _ f =>
    apply Quot.sound
    obtain ⟨k, hk, hf⟩ := exists_ge_ge (Representative.comp (Representative.id X) f).stage
      f.stage
    refine ⟨k, hk, hf, ?_⟩
    intro j hkj
    change (𝟙 _) ≫ f.comparison.hom.app _ = f.comparison.hom.app _
    exact Category.id_comp _

/-- The identity germ is a right identity for composition. -/
theorem comp_id (f : Hom X Y) : comp f (id Y) = f := by
  induction f using Quot.inductionOn with | _ f =>
    apply Quot.sound
    obtain ⟨k, hk, hf⟩ := exists_ge_ge (Representative.comp f (Representative.id Y)).stage
      f.stage
    refine ⟨k, hk, hf, ?_⟩
    intro j hkj
    change f.comparison.hom.app _ ≫ (𝟙 _) = f.comparison.hom.app _
    exact Category.comp_id _

/-- Composition of comparison germs is associative. -/
theorem assoc (f : Hom X Y) (g : Hom Y Z) (h : Hom Z W) :
    comp (comp f g) h = comp f (comp g h) := by
  induction f using Quot.inductionOn with | _ f =>
    induction g using Quot.inductionOn with | _ g =>
      induction h using Quot.inductionOn with | _ h =>
        apply Quot.sound
        obtain ⟨k, hk, hk'⟩ := exists_ge_ge
          (Representative.comp (Representative.comp f g) h).stage
          (Representative.comp f (Representative.comp g h)).stage
        refine ⟨k, hk, hk', ?_⟩
        intro j hkj
        exact Category.assoc _ _ _

end Hom

variable [directed : IsDirected I (· ≤ ·)]

include directed

variable (D c)

/-- The category of admissible approximation systems with comparison germs as morphisms. -/
def systemCategory : Cat.{u + 1, u + 1} :=
  ⟨Obj D c, {
    Hom := Hom
    id := Hom.id
    comp := Hom.comp
    id_comp := Hom.id_comp
    comp_id := Hom.comp_id
    assoc := Hom.assoc
  }⟩

/-- The carrier of the category of admissible approximation systems. -/
abbrev Systems := systemCategory (D := D) (c := c)

/-- The full category of quasi-separated finite-type spaces over the base limit. -/
abbrev quasiSeparatedFiniteTypeSpaces :=
  ObjectProperty.FullSubcategory (fun X : Over c.pt => QuasiSeparated X.hom ∧ FiniteType X.hom)

/-- The functor sending an approximation system and a comparison germ to their limits. -/
def limitFunctor : Systems (D := D) (c := c) ⥤ quasiSeparatedFiniteTypeSpaces (c := c) where
  obj X := ⟨X.limitObject, X.quasiSeparated, X.finiteType⟩
  map f := ObjectProperty.homMk (Hom.limitHom f)
  map_id X := by rfl
  map_comp f g := by
    induction f using Quot.inductionOn with | _ f =>
      induction g using Quot.inductionOn with | _ g => rfl

/-- On a representative the limit functor is its recorded compatible limit map. -/
theorem limitFunctor_map_mk {X Y : Systems (D := D) (c := c)} (f : Representative X Y) :
    ((limitFunctor (D := D) (c := c)).map (Hom.mk f)).hom = f.limitHom := rfl

variable {D c}
variable [nonempty : Nonempty I]
variable [noetherian : ∀ j : I, IsNoetherian (D.obj j)]
variable [affine : ∀ {j j' : I} (hjj' : j ≤ j'), Affine (D.map (homOfLE hjj'))]

include nonempty noetherian affine

/-- Comparisons inducing the same limit map agree on a sufficiently late tail. -/
theorem Representative.eventuallyEq_of_limitHom_eq (hc : IsLimit c)
    {X Y : Obj D c} {f g : Representative X Y} (h : f.limitHom = g.limitHom) :
    f.EventuallyEq g := by
  letI := X.quasiSeparated
  letI := X.finiteType
  letI := Y.quasiSeparated
  letI := Y.finiteType
  obtain ⟨k, hf, hg⟩ := exists_ge_ge f.stage g.stage
  let hX := le_trans f.source_le hf
  let hY := le_trans f.target_le hf
  let F := Over.map (homOfLE hf : OrderDual.toDual k ⟶ OrderDual.toDual f.stage)
  let G := Over.map (homOfLE hg : OrderDual.toDual k ⟶ OrderDual.toDual g.stage)
  let φ : InverseSystemMorphismOverBase D k
      (restrictTail hX X.diagram) (restrictTail hY Y.diagram)
      (restrictTailToBase D hX X.toBase) (restrictTailToBase D hY Y.toBase) :=
    Over.homMk (Functor.whiskerLeft F f.comparison.hom) (by
      ext j
      exact congrArg (fun η => η.app (F.obj j)) f.comparison.w)
  let ψ : InverseSystemMorphismOverBase D k
      (restrictTail hX X.diagram) (restrictTail hY Y.diagram)
      (restrictTailToBase D hX X.toBase) (restrictTailToBase D hY Y.toBase) :=
    Over.homMk (Functor.whiskerLeft G g.comparison.hom) (by
      ext j
      exact congrArg (fun η => η.app (G.obj j)) g.comparison.w)
  have hleft : f.map.left = g.map.left := congrArg (fun a => a.left) h
  obtain ⟨i, hki, hi⟩ := InverseSystemMorphismOverBase.eventually_eq_of_isLimitMorphism
    D c hc X.cone Y.cone X.toS Y.toS X.approximation Y.approximation
    f.map.left f.map.w hX hY φ ψ
    (fun j => f.compatible (F.obj j))
    (fun j => by
      change f.map.left ≫ _ = _
      rw [hleft]
      exact g.compatible (G.obj j))
  exact ⟨i, le_trans hf hki, le_trans hg hki, fun j hij => hi hij⟩

/-- Every stagewise comparison has a unique compatible morphism of limits over the base. -/
theorem Representative.existsUnique_limitMorphism (hc : IsLimit c)
    {X Y : Obj D c} (i : I) (hX : X.initial ≤ i) (hY : Y.initial ≤ i)
    (φ : InverseSystemMorphismOverBase D i
      (restrictTail hX X.diagram) (restrictTail hY Y.diagram)
      (restrictTailToBase D hX X.toBase) (restrictTailToBase D hY Y.toBase)) :
    ∃! f : X.limitObject ⟶ Y.limitObject,
      φ.IsLimitMorphism
        (Cone.whisker (Over.map (homOfLE hX : OrderDual.toDual i ⟶ OrderDual.toDual X.initial)) X.cone)
        (Cone.whisker (Over.map (homOfLE hY : OrderDual.toDual i ⟶ OrderDual.toDual Y.initial)) Y.cone) f.left := by
  let FX := Over.map (homOfLE hX : OrderDual.toDual i ⟶ OrderDual.toDual X.initial)
  let FY := Over.map (homOfLE hY : OrderDual.toDual i ⟶ OrderDual.toDual Y.initial)
  have hFY : FY.Initial := by
    apply Functor.initial_of_exists_of_isCofiltered
    · intro j
      obtain ⟨k, hik, hjk⟩ := exists_ge_ge i (OrderDual.ofDual j.left)
      exact ⟨tailObject k hik, ⟨Over.homMk (homOfLE hjk)⟩⟩
    · intro j a p q
      refine ⟨a, 𝟙 a, ?_⟩
      apply Over.OverMorphism.ext
      exact Subsingleton.elim _ _
  letI := hFY
  let hy := (Functor.Initial.isLimitWhiskerEquiv FY Y.cone).symm Y.approximation.isLimit
  let t := (Cone.postcompose φ.hom).obj (X.cone.whisker FX)
  let l : X.cone.pt ⟶ Y.cone.pt := hy.lift t
  have hl (j : Over (OrderDual.toDual i)) :
      l ≫ Y.cone.π.app (FY.obj j) = X.cone.π.app (FX.obj j) ≫ φ.hom.app j :=
    hy.fac t j
  have hover : l ≫ Y.toS = X.toS := by
    apply ((Functor.Initial.isLimitWhiskerEquiv
      (Over.forget (OrderDual.toDual i)) c).symm hc).hom_ext
    intro j
    change (l ≫ Y.toS) ≫ c.π.app j.left = X.toS ≫ c.π.app j.left
    erw [Category.assoc, ← Y.cone_toBase (FY.obj j), ← Category.assoc,
      hl j, Category.assoc]
    erw [show φ.hom.app j ≫ Y.toBase.app (FY.obj j) = X.toBase.app (FX.obj j) from
      congrArg (fun η => η.app j) φ.w]
    exact X.cone_toBase (FX.obj j)
  refine ⟨Over.homMk l hover, hl, ?_⟩
  intro f hf
  apply Over.OverMorphism.ext
  apply hy.hom_ext
  intro j
  exact (hf j).trans (hl j).symm

/-- Every quasi-separated finite-type space over the limit has an admissible approximation. -/
theorem exists_presentation (hc : IsLimit c)
    (X : quasiSeparatedFiniteTypeSpaces (c := c)) :
    ∃ Y : Systems (D := D) (c := c), Nonempty ((limitFunctor (D := D) (c := c)).obj Y ≅ X) := by
  sorry

/-- The limit functor induces a bijection on morphisms for every pair of approximation systems. -/
theorem limitFunctor_map_bijective (hc : IsLimit c) (X Y : Systems (D := D) (c := c)) :
    Function.Bijective ((limitFunctor (D := D) (c := c)).map (X := X) (Y := Y)) := by
  constructor
  · intro f g h
    induction f using Quot.inductionOn with | _ f =>
      induction g using Quot.inductionOn with | _ g =>
        apply Quot.sound
        apply Representative.eventuallyEq_of_limitHom_eq hc
        exact congrArg (fun a => a.hom) h
  · intro f
    letI := X.quasiSeparated
    letI := X.finiteType
    letI := Y.quasiSeparated
    letI := Y.finiteType
    obtain ⟨i, hX, hY, φ, hφ⟩ := FiniteTypeApproximationLimitSystem.exists_morphism
      D c hc X.cone Y.cone X.toS Y.toS X.approximation Y.approximation
      f.hom.left f.hom.w
    exact ⟨Hom.mk ⟨i, hX, hY, φ, f.hom, hφ⟩, rfl⟩

end AlgebraicGeometry.AlgebraicSpace.FiniteTypeApproximation

namespace AlgebraicGeometry.AlgebraicSpace.FiniteTypeApproximation

/-- The limit functor is an equivalence over a directed affine limit of Noetherian spaces. -/
theorem limitFunctor_isEquivalence
    {I : Type u} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
    {S : Scheme.{u}} (D : OrderDual I ⥤ AlgebraicSpace S) (c : Cone D)
    (hc : IsLimit c)
    [∀ j : I, IsNoetherian (D.obj j)]
    [∀ {j j' : I} (hjj' : j ≤ j'), Affine (D.map (homOfLE hjj'))] :
    (limitFunctor D c).IsEquivalence := by
  exact {
    faithful := ⟨fun {X Y} => (limitFunctor_map_bijective hc X Y).1⟩
    full := ⟨fun {X Y} => (limitFunctor_map_bijective hc X Y).2⟩
    essSurj := ⟨exists_presentation hc⟩
  }

end AlgebraicGeometry.AlgebraicSpace.FiniteTypeApproximation

namespace AlgebraicGeometry.AlgebraicSpace

namespace FiniteTypeApproximationLimitSystem

/-- Two finite-type approximation systems of the same quasi-separated finite-type
algebraic space over a directed affine limit admit comparison morphisms on a common
tail that induce the identity on the limit and are mutually inverse at every
sufficiently late stage. -/
@[stacks 0CPB]
theorem exists_morphisms_eventually_inverse
    {I : Type u} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
    {S : Scheme.{u}} (D : OrderDual I ⥤ AlgebraicSpace S) (c : Cone D) (hc : IsLimit c)
    [∀ j : I, IsNoetherian (D.obj j)]
    [∀ {j j' : I} (hjj' : j ≤ j'), Affine (D.map (homOfLE hjj'))]
    (X : AlgebraicSpace S) {i₁ i₂ : I}
    {Xsys : Over (OrderDual.toDual i₁) ⥤ AlgebraicSpace S}
    {Ysys : Over (OrderDual.toDual i₂) ⥤ AlgebraicSpace S}
    (xπ : (Functor.const (Over (OrderDual.toDual i₁))).obj X ⟶ Xsys)
    (yπ : (Functor.const (Over (OrderDual.toDual i₂))).obj X ⟶ Ysys)
    (toS : X ⟶ c.pt)
    [QuasiSeparated toS] [FiniteType toS]
    (Xapprox : FiniteTypeApproximationLimitSystem D c i₁ Xsys
      (⟨X, xπ⟩ : Cone Xsys) toS)
    (Yapprox : FiniteTypeApproximationLimitSystem D c i₂ Ysys
      (⟨X, yπ⟩ : Cone Ysys) toS) :
    ∃ (i₀ : I) (hi₁ : i₁ ≤ i₀) (hi₂ : i₂ ≤ i₀),
      ∃ φ : InverseSystemMorphismOverBase D i₀
          (restrictTail hi₁ Xsys) (restrictTail hi₂ Ysys)
          (restrictTailToBase D hi₁ Xapprox.toBase)
          (restrictTailToBase D hi₂ Yapprox.toBase),
        φ.IsLimitMorphism
          (Cone.whisker (Over.map (homOfLE hi₁ : OrderDual.toDual i₀ ⟶ OrderDual.toDual i₁))
            (⟨X, xπ⟩ : Cone Xsys))
          (Cone.whisker (Over.map (homOfLE hi₂ : OrderDual.toDual i₀ ⟶ OrderDual.toDual i₂))
            (⟨X, yπ⟩ : Cone Ysys)) (𝟙 X) ∧
        ∃ ψ : InverseSystemMorphismOverBase D i₀
            (restrictTail hi₂ Ysys) (restrictTail hi₁ Xsys)
            (restrictTailToBase D hi₂ Yapprox.toBase)
            (restrictTailToBase D hi₁ Xapprox.toBase),
          ψ.IsLimitMorphism
            (Cone.whisker (Over.map (homOfLE hi₂ : OrderDual.toDual i₀ ⟶ OrderDual.toDual i₂))
              (⟨X, yπ⟩ : Cone Ysys))
            (Cone.whisker (Over.map (homOfLE hi₁ : OrderDual.toDual i₀ ⟶ OrderDual.toDual i₁))
              (⟨X, xπ⟩ : Cone Xsys)) (𝟙 X) ∧
          ∃ (i : I) (hi₀i : i₀ ≤ i), ∀ {j : I} (hij : i ≤ j),
            (InverseSystemMorphismOverBase.comp φ ψ).hom.app
                (tailObject j (le_trans hi₀i hij)) = 𝟙 _ ∧
            (InverseSystemMorphismOverBase.comp ψ φ).hom.app
                (tailObject j (le_trans hi₀i hij)) = 𝟙 _ :=
  by
    obtain ⟨k, hk₁, hk₂, φ, hφ⟩ := exists_morphism D c hc
      (⟨X, xπ⟩ : Cone Xsys) (⟨X, yπ⟩ : Cone Ysys) toS toS Xapprox Yapprox
      (𝟙 X) (Category.id_comp _)
    obtain ⟨l, hl₂, hl₁, ψ, hψ⟩ := exists_morphism D c hc
      (⟨X, yπ⟩ : Cone Ysys) (⟨X, xπ⟩ : Cone Xsys) toS toS Yapprox Xapprox
      (𝟙 X) (Category.id_comp _)
    obtain ⟨i₀, hki₀, hli₀⟩ := exists_ge_ge k l
    let hi₁ := le_trans hk₁ hki₀
    let hi₂ := le_trans hk₂ hki₀
    let F := Over.map (homOfLE hki₀ : OrderDual.toDual i₀ ⟶ OrderDual.toDual k)
    let G := Over.map (homOfLE hli₀ : OrderDual.toDual i₀ ⟶ OrderDual.toDual l)
    let φ' : InverseSystemMorphismOverBase D i₀
        (restrictTail hi₁ Xsys) (restrictTail hi₂ Ysys)
        (restrictTailToBase D hi₁ Xapprox.toBase)
        (restrictTailToBase D hi₂ Yapprox.toBase) :=
      Over.homMk (Functor.whiskerLeft F φ.hom) (by
        ext j
        exact congrArg (fun η => η.app (F.obj j)) φ.w)
    let ψ' : InverseSystemMorphismOverBase D i₀
        (restrictTail hi₂ Ysys) (restrictTail hi₁ Xsys)
        (restrictTailToBase D hi₂ Yapprox.toBase)
        (restrictTailToBase D hi₁ Xapprox.toBase) :=
      Over.homMk (Functor.whiskerLeft G ψ.hom) (by
        ext j
        exact congrArg (fun η => η.app (G.obj j)) ψ.w)
    let A : FiniteTypeApproximation.Obj D c :=
      ⟨i₁, Xsys, ⟨X, xπ⟩, toS, inferInstance, inferInstance, Xapprox⟩
    let B : FiniteTypeApproximation.Obj D c :=
      ⟨i₂, Ysys, ⟨X, yπ⟩, toS, inferInstance, inferInstance, Yapprox⟩
    let f : FiniteTypeApproximation.Representative A B :=
      ⟨i₀, hi₁, hi₂, φ', 𝟙 (Over.mk toS), fun j => hφ (F.obj j)⟩
    let g : FiniteTypeApproximation.Representative B A :=
      ⟨i₀, hi₂, hi₁, ψ', 𝟙 (Over.mk toS), fun j => hψ (G.obj j)⟩
    obtain ⟨a, ha, _, hfg⟩ :=
      FiniteTypeApproximation.Representative.eventuallyEq_of_limitHom_eq hc
        (f := FiniteTypeApproximation.Representative.comp f g)
        (g := FiniteTypeApproximation.Representative.id A) (by
          change (𝟙 (Over.mk toS)) ≫ (𝟙 _) = 𝟙 _
          exact Category.id_comp _)
    obtain ⟨b, hb, _, hgf⟩ :=
      FiniteTypeApproximation.Representative.eventuallyEq_of_limitHom_eq hc
        (f := FiniteTypeApproximation.Representative.comp g f)
        (g := FiniteTypeApproximation.Representative.id B) (by
          change (𝟙 (Over.mk toS)) ≫ (𝟙 _) = 𝟙 _
          exact Category.id_comp _)
    obtain ⟨m, ham, hbm⟩ := exists_ge_ge a b
    have hi₀a : i₀ ≤ a :=
      le_trans (Classical.choose_spec (exists_ge_ge f.stage g.stage)).1 ha
    refine ⟨i₀, hi₁, hi₂, φ', (fun j => hφ (F.obj j)),
      ψ', (fun j => hψ (G.obj j)), m, le_trans hi₀a ham, ?_⟩
    intro j hmj
    exact ⟨hfg j (le_trans ham hmj), hgf j (le_trans hbm hmj)⟩

end FiniteTypeApproximationLimitSystem

end AlgebraicGeometry.AlgebraicSpace
