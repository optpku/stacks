module

public import ReasLib.AlgebraicTopology.SimplicialObject.Splitting
public import Mathlib.AlgebraicTopology.SimplicialSet.Splitting
public import Mathlib.CategoryTheory.Widesubcategory
public import Mathlib.Tactic.CrossRefAttribute

/-!
@stack 017R

# Morphisms between the nondegenerate splittings of simplicial sets

The canonical splitting `SSet.splitting` turns a simplicial map that preserves nondegenerate
simplices into a morphism of split simplicial objects. The generic property-transfer API for
split simplicial objects then applies without a chapter-specific splitting wrapper.
-/

@[expose] public section

open CategoryTheory Opposite Simplicial

universe u

noncomputable section

namespace CategoryTheory.SimplicialObject.Splitting

variable {U : SSet.{u}}

/-- The distinguished map in every splitting of a simplicial set is injective. -/
@[stacks 017R "injectivity of splitting summands"]
theorem inclusion_injective (s : Splitting U) (n : ℕ) :
    Function.Injective (s.ι n) := sorry

/-- Every splitting of a simplicial set represents its distinguished summands by subobjects. -/
@[stacks 017R "splittings of simplicial sets are monic"]
instance isMonic (s : Splitting U) : s.IsMonic := sorry

/-- The image of the distinguished summand of any splitting is exactly the set of
nondegenerate simplices. -/
@[stacks 017R "uniqueness of the nondegenerate summand"]
theorem inclusion_range (s : Splitting U) (n : ℕ) :
    Set.range (s.ι n) = U.nonDegenerate n := sorry

/-- A simplex belongs to the nondegenerate part exactly when it has a unique preimage in the
distinguished summand of any splitting. -/
@[stacks 017R "unique representation by a splitting summand"]
theorem mem_nonDegenerate_iff_existsUnique (s : Splitting U) (n : ℕ)
    {x : U _⦋n⦌} :
    x ∈ U.nonDegenerate n ↔ ∃! y : s.N n, s.ι n y = x := sorry

/-- Every distinguished summand simplex is nondegenerate. -/
@[stacks 017R "membership of a splitting summand in the nondegenerate simplices"]
theorem inclusion_mem_nonDegenerate (s : Splitting U) (n : ℕ) (x : s.N n) :
    s.ι n x ∈ U.nonDegenerate n := sorry

/-- Any two splittings of a simplicial set determine the same distinguished subobject in each
degree. -/
@[stacks 017R "uniqueness of splitting subobjects"]
theorem subobject_eq (s t : Splitting U) (n : ℕ) :
    s.subobject n = t.subobject n := sorry

end CategoryTheory.SimplicialObject.Splitting

namespace SSet

/-- Every simplicial set admits a splitting by its nondegenerate simplices. -/
@[stacks 017R "existence of the nondegenerate splitting"]
theorem isSplit (U : SSet.{u}) :
    CategoryTheory.SimplicialObject.IsSplit U := sorry

/-- A simplicial-set morphism preserves nondegenerate simplices when the image of every
nondegenerate simplex is nondegenerate in the same degree. -/
@[stacks 017S "preservation of nondegenerate simplices"]
def preservesNondegenerate : MorphismProperty SSet.{u} :=
  fun {U V} f ↦ ∀ ⦃n : ℕ⦄ (x : U.nonDegenerate n),
    f.app (op ⦋n⦌) x ∈ V.nonDegenerate n

/-- Simplicial maps preserving nondegenerate simplices contain identities and are closed under
composition. -/
@[stacks 017S "multiplicativity of nondegenerate-simplex preservation"]
instance preservesNondegenerate.isMultiplicative :
    preservesNondegenerate.IsMultiplicative := sorry

/-- Preservation of nondegenerate simplices is invariant under pre- and postcomposition by
isomorphisms. -/
@[stacks 017S "isomorphism invariance of nondegenerate-simplex preservation"]
instance preservesNondegenerate.respectsIso :
    preservesNondegenerate.RespectsIso := sorry

variable {U V : SSet.{u}}

namespace nonDegenerate

/-- The map on nondegenerate simplices induced by a simplicial-set morphism that preserves
nondegenerate simplices. -/
@[stacks 017S "map on nondegenerate simplices"]
def map (f : U ⟶ V)
    (hPreserves : preservesNondegenerate f)
    (n : ℕ) : U.nonDegenerate n → V.nonDegenerate n :=
  fun x ↦ ⟨f.app (op ⦋n⦌) x, hPreserves x⟩

/-- The underlying simplex of `nonDegenerate.map f hPreserves n x` is the image of `x` under the
degree-`n` component of `f`. -/
@[simp, stacks 017S "nondegenerate simplex map formula"]
theorem map.apply (f : U ⟶ V)
    (hPreserves : preservesNondegenerate f)
    {n : ℕ} (x : U.nonDegenerate n) :
    (map f hPreserves n x).1 = f.app (op ⦋n⦌) x := sorry

namespace map

/-- The map on nondegenerate simplices induced by an identity is the identity. -/
@[simp, stacks 017S "identity law for maps on nondegenerate simplices"]
theorem id (U : SSet.{u}) (n : ℕ) :
    nonDegenerate.map (𝟙 U) (preservesNondegenerate.id_mem U) n = _root_.id := sorry

/-- Maps on nondegenerate simplices respect composition. -/
@[simp, stacks 017S "composition law for maps on nondegenerate simplices"]
theorem comp {W : SSet.{u}} (f : U ⟶ V) (g : V ⟶ W)
    (hf : preservesNondegenerate f) (hg : preservesNondegenerate g) (n : ℕ) :
    nonDegenerate.map (f ≫ g) (preservesNondegenerate.comp_mem f g hf hg) n =
      nonDegenerate.map g hg n ∘ nonDegenerate.map f hf n := sorry

/-- A map preserving nondegenerate simplices is injective in every degree exactly when all its
maps on nondegenerate simplices are injective. -/
@[stacks 017S "injectivity detected on nondegenerate simplices"]
theorem injective_iff (f : U ⟶ V) (hPreserves : preservesNondegenerate f) :
    (∀ n : ℕ, Function.Injective (nonDegenerate.map f hPreserves n)) ↔
      ∀ n : ℕ, Function.Injective (f.app (op ⦋n⦌)) := sorry

/-- A map preserving nondegenerate simplices is surjective in every degree exactly when all its
maps on nondegenerate simplices are surjective. -/
@[stacks 017S "surjectivity detected on nondegenerate simplices"]
theorem surjective_iff (f : U ⟶ V) (hPreserves : preservesNondegenerate f) :
    (∀ n : ℕ, Function.Surjective (nonDegenerate.map f hPreserves n)) ↔
      ∀ n : ℕ, Function.Surjective (f.app (op ⦋n⦌)) := sorry

/-- A map preserving nondegenerate simplices is bijective in every degree exactly when all its
maps on nondegenerate simplices are bijective. -/
@[stacks 017S "bijectivity detected on nondegenerate simplices"]
theorem bijective_iff (f : U ⟶ V) (hPreserves : preservesNondegenerate f) :
    (∀ n : ℕ, Function.Bijective (nonDegenerate.map f hPreserves n)) ↔
      ∀ n : ℕ, Function.Bijective (f.app (op ⦋n⦌)) := sorry

end map

end nonDegenerate

namespace splitting

/-- The distinguished carrier of the canonical splitting is canonically the type of
nondegenerate simplices in each degree. -/
@[stacks 017R "canonical nondegenerate carrier equivalence"]
def nonDegenerateEquiv (U : SSet.{u}) (n : ℕ) :
    U.splitting.N n ≃ U.nonDegenerate n :=
  Equiv.cast (SSet.splitting_N U n)

/-- The canonical carrier equivalence forgets to the distinguished splitting inclusion. -/
@[simp, stacks 017R "canonical nondegenerate carrier equivalence application"]
theorem nonDegenerateEquiv_apply (U : SSet.{u}) (n : ℕ) (x : U.splitting.N n) :
    (nonDegenerateEquiv U n x).1 = U.splitting.ι n x := sorry

/-- The inverse carrier equivalence followed by the distinguished inclusion recovers the
underlying nondegenerate simplex. -/
@[simp, stacks 017R "inverse canonical nondegenerate carrier equivalence application"]
theorem nonDegenerateEquiv.symm_apply_ι (U : SSet.{u}) (n : ℕ)
    (x : U.nonDegenerate n) :
    U.splitting.ι n ((nonDegenerateEquiv U n).symm x) = x := sorry

/-- The canonical morphism between the distinguished summands of the Mathlib splittings in one
degree, transported through the named equivalences with nondegenerate-simplex types. -/
@[stacks 017S "map on splitting summands"]
def summandMap (f : U ⟶ V)
    (hPreserves : preservesNondegenerate f)
    (n : ℕ) : U.splitting.N n ⟶ V.splitting.N n :=
  (Equiv.toIso (nonDegenerateEquiv U n)).hom ≫
    ↾(SSet.nonDegenerate.map f hPreserves n) ≫
      (Equiv.toIso (nonDegenerateEquiv V n)).inv

/-- Under the canonical carrier equivalences, the summand map is exactly the map on
nondegenerate simplices. -/
@[stacks 017S "naturality of the canonical nondegenerate carrier equivalence"]
theorem nonDegenerateEquiv.naturality (f : U ⟶ V)
    (hPreserves : preservesNondegenerate f) (n : ℕ) (x : U.splitting.N n) :
    nonDegenerateEquiv V n (summandMap f hPreserves n x) =
      SSet.nonDegenerate.map f hPreserves n (nonDegenerateEquiv U n x) := sorry

/-- The map on nondegenerate simplices commutes with the inclusions of the distinguished
summands into the underlying simplicial sets. -/
@[stacks 017S "splitting summand map naturality"]
theorem summandMap.comm (f : U ⟶ V)
    (hPreserves : preservesNondegenerate f)
    (n : ℕ) :
    U.splitting.ι n ≫ f.app (op ⦋n⦌) =
      summandMap f hPreserves n ≫ V.splitting.ι n := sorry

/-- The canonical morphism between the split simplicial sets obtained from the nondegenerate
splittings of two simplicial sets. -/
@[stacks 017S "morphism between nondegenerate splittings"]
def hom (f : U ⟶ V)
    (hPreserves : preservesNondegenerate f) :
    SimplicialObject.Split.mk' U.splitting ⟶ SimplicialObject.Split.mk' V.splitting where
  F := f
  f := summandMap f hPreserves
  comm := summandMap.comm f hPreserves

/-- The morphism between canonical nondegenerate splittings induced by an identity is the
identity morphism. -/
@[stacks 017S "identity law for nondegenerate splittings"]
theorem hom.id (U : SSet.{u}) :
    hom (𝟙 U) (preservesNondegenerate.id_mem U) =
      𝟙 (SimplicialObject.Split.mk' U.splitting) := sorry

/-- The morphism between canonical nondegenerate splittings induced by a composite is the
composite of the induced morphisms. -/
@[stacks 017S "composition law for nondegenerate splittings"]
theorem hom.comp {W : SSet.{u}} (f : U ⟶ V) (g : V ⟶ W)
    (hf : preservesNondegenerate f) (hg : preservesNondegenerate g) :
    hom (f ≫ g) (preservesNondegenerate.comp_mem f g hf hg) =
      hom f hf ≫ hom g hg := sorry

/-- The canonical nondegenerate splitting is functorial on the wide subcategory of simplicial
sets and maps preserving nondegenerate simplices. -/
@[stacks 017S "functorial nondegenerate splitting"]
def functor :
    WideSubcategory preservesNondegenerate.{u} ⥤ SimplicialObject.Split (Type u) where
  obj U := SimplicialObject.Split.mk' U.obj.splitting
  map f := hom f.hom f.property
  map_id U := hom.id U.obj
  map_comp f g := hom.comp f.hom g.hom f.property g.property

end splitting

end SSet
