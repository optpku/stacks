module

public import ReasLib.Topology.Counterexamples.TwoClosedPoints.Basic
public import Mathlib.Algebra.Category.Grp.AB
public import Mathlib.Algebra.Category.Grp.Zero
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Mathlib.CategoryTheory.Sites.GlobalSections
public import Mathlib.Topology.Sheaves.AddCommGrpCat
public import Mathlib.Topology.Sheaves.Functors
public import ReasLib.Topology.Sheaf.Skyscraper

/-!
# The two-closed-points sheaf system

This module packages the filtered system of tail sheaves on
`TopCat.Counterexample.TwoClosedPoints.space`.  The system is parameterized by its value object in
`AddCommGrpCat`; the integer-valued construction in the Stacks Project is a specialization.

The section objects are categorical products and all reindexing maps use `Pi.map'`, so the API
does not duplicate the additive-function implementation already provided by `AddCommGrpCat`.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace TopCat.Sheaf

noncomputable section

universe u

namespace TopCat.Counterexample.TwoClosedPoints

/-- The stalk functor at a point of the two-closed-points space. -/
abbrev stalkFunctor {C : Type u} [Category.{0} C] [HasColimits C]
    (x : space) : space.Sheaf C ⥤ C :=
  TopCat.Sheaf.forget C space ⋙ TopCat.Presheaf.stalkFunctor C x

/-- The global-sections functor on the two-closed-points space. -/
abbrev globalSections {C : Type u} [Category.{0} C] : space.Sheaf C ⥤ C :=
  (sheafSections (Opens.grothendieckTopology space) C).obj (op ⊤)

namespace Tail

variable (A : AddCommGrpCat)

include A

/-- The generic indices in the tail beginning at `n` which lie in an ambient open `U`. -/
abbrev index (n : ℕ) (U : Opens space) : Type :=
  {m : ℕ // n ≤ m ∧ Point.generic m ∈ U}

/-- The map of tail indices induced by restricting an ambient open. -/
def indexMap (n : ℕ) {U V : Opens space} (i : U ≤ V) :
    index n U → index n V :=
  fun x ↦ ⟨x.1, x.2.1, i x.2.2⟩

/-- The `A`-valued sections of the tail beginning at `n` over an ambient open `U`. -/
abbrev sections (n : ℕ) (U : Opens space) : AddCommGrpCat :=
  ∏ᶜ fun _ : index n U ↦ A

/-- Restriction of tail sections along an inclusion of ambient opens. -/
def restrict (n : ℕ) {U V : Opens space} (i : U ≤ V) :
    sections A n V ⟶ sections A n U :=
  Pi.map' (indexMap n i) (fun _ ↦ 𝟙 A)

/-- Tail restriction along an identity inclusion is the identity. -/
theorem restrict_id (n : ℕ) (U : Opens space) :
    restrict A n (le_refl U) = 𝟙 (sections A n U) := sorry

/-- Tail restrictions compose along nested ambient opens. -/
theorem restrict_comp (n : ℕ) {U V W : Opens space} (i : U ≤ V) (j : V ≤ W) :
    restrict A n (i.trans j) = restrict A n j ≫ restrict A n i := sorry

/-- The identity law in the opposite category of ambient opens for tail restrictions. -/
theorem restrict_op_id (n : ℕ) (U : (Opens space)ᵒᵖ) :
    restrict A n (𝟙 U).unop.le = 𝟙 (sections A n U.unop) := sorry

/-- The composition law in the opposite category of ambient opens for tail restrictions. -/
theorem restrict_op_comp (n : ℕ) {U V W : (Opens space)ᵒᵖ}
    (i : U ⟶ V) (j : V ⟶ W) :
    restrict A n (i ≫ j).unop.le =
      restrict A n i.unop.le ≫ restrict A n j.unop.le := sorry

/-- The presheaf whose sections are `A`-valued functions on the generic tail. -/
def presheaf (n : ℕ) : space.Presheaf AddCommGrpCat where
  obj U := sections A n U.unop
  map {_ _} i := restrict A n i.unop.le
  map_id U := restrict_op_id A n U
  map_comp i j := restrict_op_comp A n i j

/-- The tail presheaf satisfies the sheaf condition. -/
theorem presheaf_isSheaf (n : ℕ) : (presheaf A n).IsSheaf := sorry

/-- The sheaf of `A`-valued sections supported on the generic tail beginning at `n`. -/
def sheaf (n : ℕ) : space.Sheaf AddCommGrpCat :=
  ⟨presheaf A n, presheaf_isSheaf A n⟩

/-- The constant `A`-sheaf on the tail subspace. -/
abbrev constantSheaf (n : ℕ) : (tailSpace n).Sheaf AddCommGrpCat :=
  (CategoryTheory.constantSheaf (Opens.grothendieckTopology (tailSpace n)) AddCommGrpCat).obj A

/-- The canonical pushforward of the constant `A`-sheaf from the tail subspace. -/
abbrev canonicalSheaf (n : ℕ) : space.Sheaf AddCommGrpCat :=
  (pushforward AddCommGrpCat (tailInclusion n)).obj (constantSheaf A n)

/-- The explicit tail sheaf is isomorphic to the canonical pushforward of the constant tail sheaf. -/
theorem sheaf_isIsomorphic_canonical (n : ℕ) :
    IsIsomorphic (sheaf A n) (canonicalSheaf A n) := sorry

/-- The map of tail indices induced by discarding the first part of a tail. -/
def stageIndexMap {i j : ℕ} (h : i ≤ j) (U : Opens space) :
    index j U → index i U :=
  fun x ↦ ⟨x.1, le_trans h x.2.1, x.2.2⟩

/-- The stage transition on sections obtained by discarding the initial part of a tail. -/
def sectionMap {i j : ℕ} (h : i ≤ j) (U : Opens space) :
    sections A i U ⟶ sections A j U :=
  Pi.map' (stageIndexMap h U) (fun _ ↦ 𝟙 A)

/-- Stage transitions commute with restriction of ambient opens. -/
theorem sectionMap_naturality {i j : ℕ} (h : i ≤ j)
    {U V : (Opens space)ᵒᵖ} (f : U ⟶ V) :
    (presheaf A i).map f ≫ sectionMap A h V.unop =
      sectionMap A h U.unop ≫ (presheaf A j).map f := sorry

/-- The transition from the sheaf on tail `i` to the sheaf on tail `j` for `i ≤ j`. -/
def transition {i j : ℕ} (h : i ≤ j) : sheaf A i ⟶ sheaf A j :=
  ObjectProperty.homMk
    { app := fun U ↦ sectionMap A h U.unop
      naturality := fun _ _ f ↦ sectionMap_naturality A h f }

/-- Tail transitions are identities at equal stages. -/
theorem transition_id (n : ℕ) :
    transition A (le_refl n) = 𝟙 (sheaf A n) := sorry

/-- Tail transitions compose according to transitivity of their stage inequalities. -/
theorem transition_comp {i j k : ℕ} (hij : i ≤ j) (hjk : j ≤ k) :
    transition A (hij.trans hjk) = transition A hij ≫ transition A hjk := sorry

/-- The product of copies of `A` indexed by the tail beginning at `n`. -/
abbrev product (n : ℕ) : AddCommGrpCat :=
  ∏ᶜ fun _ : {m : ℕ // n ≤ m} ↦ A

/-- The reindexing map between tail products induced by an inequality of stages. -/
def productMap {i j : ℕ} (h : i ≤ j) : product A i ⟶ product A j :=
  Pi.map' (fun x : {m : ℕ // j ≤ m} ↦ ⟨x.1, le_trans h x.2⟩) (fun _ ↦ 𝟙 A)

/-- Tail-product transitions are identities at equal stages. -/
theorem productMap_id (n : ℕ) :
    productMap A (le_refl n) = 𝟙 (product A n) := sorry

/-- Tail-product transitions compose according to transitivity. -/
theorem productMap_comp {i j k : ℕ} (hij : i ≤ j) (hjk : j ≤ k) :
    productMap A (hij.trans hjk) = productMap A hij ≫ productMap A hjk := sorry

/-- The direct system of tail products. -/
def productFunctor : ℕ ⥤ AddCommGrpCat where
  obj n := product A n
  map h := productMap A h.down.down
  map_id n := productMap_id A n
  map_comp f g := productMap_comp A f.down.down g.down.down

/-- The eventual-value colimit of the tail-product system. -/
abbrev eventualColimit : AddCommGrpCat :=
  colimit (productFunctor A)

/-- The direct system of tail sheaves. -/
@[stacks 01BT "filtered diagram"]
def sheafFunctor : ℕ ⥤ space.Sheaf AddCommGrpCat where
  obj n := sheaf A n
  map h := transition A h.down.down
  map_id n := transition_id A n
  map_comp f g := transition_comp A f.down.down g.down.down

/-- The colimit sheaf of the direct system of tail sheaves. -/
abbrev sheafColimit : space.Sheaf AddCommGrpCat :=
  colimit (sheafFunctor A)

/-- The binary biproduct of skyscraper sheaves at the two closed points with eventual value `A`. -/
abbrev skyscraperPair : space.Sheaf AddCommGrpCat :=
  biprod
    (TopCat.Sheaf.Skyscraper.atPoint firstPoint (eventualColimit A))
    (TopCat.Sheaf.Skyscraper.atPoint secondPoint (eventualColimit A))

/-- A tail sheaf has zero stalk at a generic point before that point enters the tail. -/
theorem sheaf_stalk_generic_isZero {m n : ℕ} (h : m < n) :
    IsZero ((stalkFunctor (genericPoint m)).obj (sheaf A n)) := sorry

/-- Every generic-point stalk of the tail-sheaf colimit is zero. -/
theorem sheafColimit_stalk_generic_isZero (m : ℕ) :
    IsZero ((stalkFunctor (genericPoint m)).obj (sheafColimit A)) := sorry

/-- The eventual tail-product colimit is nonzero whenever its value object is nonzero. -/
theorem eventualColimit_not_isZero_of_not_isZero (hA : ¬ IsZero A) :
    ¬ IsZero (eventualColimit A) := sorry

/-- A nontrivial coefficient group has a nonzero eventual tail-product colimit. -/
theorem eventualColimit_not_isZero_of_nontrivial [Nontrivial A] :
    ¬ IsZero (eventualColimit A) := sorry

/-- The first closed-point stalk of the tail-sheaf colimit is its eventual tail-product colimit. -/
theorem sheafColimit_stalk_first_isIsomorphic :
    IsIsomorphic ((stalkFunctor firstPoint).obj (sheafColimit A)) (eventualColimit A) := sorry

/-- The second closed-point stalk of the tail-sheaf colimit is its eventual tail-product colimit. -/
theorem sheafColimit_stalk_second_isIsomorphic :
    IsIsomorphic ((stalkFunctor secondPoint).obj (sheafColimit A)) (eventualColimit A) := sorry

/-- The tail-sheaf colimit is the pair of skyscraper sheaves at the two closed points. -/
theorem sheafColimit_isIsomorphic_skyscraperPair :
    IsIsomorphic (sheafColimit A) (skyscraperPair A) := sorry

/-- Global sections of the tail-sheaf colimit are the binary biproduct of the eventual colimit. -/
theorem sheafColimit_globalSections_isIsomorphic :
    IsIsomorphic (globalSections.obj (sheafColimit A))
      (eventualColimit A ⊞ eventualColimit A) := sorry

/-- The direct system obtained by taking global sections of tail sheaves. -/
abbrev globalSectionsFunctor : ℕ ⥤ AddCommGrpCat :=
  sheafFunctor A ⋙ globalSections

/-- The colimit of the stagewise global sections is the eventual tail-product colimit. -/
theorem globalSectionsColimit_isIsomorphic :
    IsIsomorphic (colimit (globalSectionsFunctor A)) (eventualColimit A) := sorry

/-- The canonical comparison from the colimit of global sections to global sections of the sheaf
colimit. -/
@[stacks 01BT "comparison morphism"]
abbrev globalSectionsComparison :
    colimit (globalSectionsFunctor A) ⟶
      globalSections.obj (sheafColimit A) :=
  colimit.post (sheafFunctor A) globalSections

/-- If the eventual tail-product colimit is nonzero, global sections do not preserve this filtered
colimit of tail sheaves. -/
theorem globalSectionsComparison_not_isIso (hA : ¬ IsZero (eventualColimit A)) :
    ¬ IsIso (globalSectionsComparison A) := sorry

/-- Global sections fail to preserve the tail-sheaf colimit for every nontrivial coefficient
group. -/
@[stacks 01BT "counterexample"]
theorem globalSectionsComparison_not_isIso_of_nontrivial [Nontrivial A] :
    ¬ IsIso (globalSectionsComparison A) := sorry

end Tail

end TopCat.Counterexample.TwoClosedPoints

end
