module

public import ReasLib.CategoryTheory.Sites.Family
public import ReasLib.CategoryTheory.Sites.Sheaf.Types.Colimits
public import ReasLib.CategoryTheory.Sites.SheafifiedRepresentable.Hom
public import Mathlib.CategoryTheory.Sites.ConstantSheaf

/-!
# Coproducts of sheafified representables

This leaf owns the canonical coproduct of the sheafified representables attached
to an indexed family of objects. Finiteness is a property of a family and belongs
in the statements that require it, rather than in the coproduct construction.
-/

@[expose] public section

noncomputable section

open CategoryTheory Limits Opposite

universe w u v

namespace CategoryTheory.GrothendieckTopology

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)

/-- The coproduct of the sheafified representables attached to an indexed family. -/
noncomputable def sheafifiedRepresentableCoproduct
    [HasWeakSheafify J (Type (max w u v))]
    (𝒰 : Limits.FormalCoproduct.{w} C) :
    Sheaf J (Type (max w u v)) :=
  ∐ fun i : 𝒰.index ↦ J.uliftSheafifiedRepresentable.{w} (𝒰.obj i)


section DisjointCover

variable [HasWeakSheafify J (Type (max w u v))]
variable {ι : Type (max w u v)} {X : ι → C} (c : Cofan X)

/-- A cocone gives a local section on each member of the generated covering sieve. -/
def sheafifiedRepresentableCoconeFamily
    (s : Cofan fun i ↦ J.uliftSheafifiedRepresentable.{w} (X i)) :
    Presieve.FamilyOfElements s.pt.obj (Sieve.ofArrows X c.inj).arrows :=
  fun {Y} f hf ↦ s.pt.obj.map (Sieve.ofArrows.h hf).op
    (J.uliftSheafifiedRepresentableHomEquiv s.pt _ (s.inj (Sieve.ofArrows.i hf)))

/-- Disjoint covering components make the locally specified sections compatible. -/
theorem sheafifiedRepresentableCoconeFamily_compatible
    [∀ i, Mono (c.inj i)]
    (hdisj : ∀ {i j : ι}, i ≠ j → ∀ {Y : C} (a : Y ⟶ X i) (b : Y ⟶ X j),
      a ≫ c.inj i = b ≫ c.inj j → (⊥ : Sieve Y) ∈ J Y)
    (s : Cofan fun i ↦ J.uliftSheafifiedRepresentable.{w} (X i)) :
    (J.sheafifiedRepresentableCoconeFamily c s).Compatible := sorry

/-- A disjoint covering family is a coproduct after sheafification; the descent map
uses the actual sheaf amalgamation of the sections specified on each component. -/
def isColimitSheafifiedRepresentableCofan
    (hcov : Sieve.ofArrows X c.inj ∈ J c.pt) [∀ i, Mono (c.inj i)]
    (hdisj : ∀ {i j : ι}, i ≠ j → ∀ {Y : C} (a : Y ⟶ X i) (b : Y ⟶ X j),
      a ≫ c.inj i = b ≫ c.inj j → (⊥ : Sieve Y) ∈ J Y) :
    IsColimit (Cofan.mk (J.uliftSheafifiedRepresentable.{w} c.pt)
      (fun i ↦ J.uliftSheafifiedRepresentableMap (c.inj i))) :=
  Cofan.IsColimit.mk _
    (fun s ↦ (J.uliftSheafifiedRepresentableHomEquiv s.pt c.pt).symm
      (((isSheaf_iff_isSheaf_of_type J s.pt.obj).mp s.pt.property) _ hcov |>.amalgamate
        (J.sheafifiedRepresentableCoconeFamily c s)
        (J.sheafifiedRepresentableCoconeFamily_compatible c hdisj s)))
    (fun _ _ ↦ sorry) (fun _ _ _ ↦ sorry)

end DisjointCover

section Constant

variable [HasWeakSheafify J (Type (max w u v))]
variable {T : C} (hT : IsTerminal T) (I : Type (max w u v))

/-- The constant sheaf is the coproduct of copies of the terminal representable,
with the `i`th injection specified by the constant section with value `i`. -/
def constantSheafCofan : Cofan fun _ : I ↦ J.uliftSheafifiedRepresentable.{w} T :=
  Cofan.mk ((constantSheaf J (Type (max w u v))).obj I) (fun i ↦
    (J.uliftSheafifiedRepresentableHomEquiv _ T).symm
      (((sheafificationAdjunction J (Type (max w u v))).unit.app
        ((Functor.const Cᵒᵖ).obj I)).app (op T) i))

/-- Descent from the constant sheaf sends each label to the corresponding terminal section. -/
def isColimitConstantSheafCofan : IsColimit (J.constantSheafCofan (T := T) I) :=
  Cofan.IsColimit.mk _
    (fun s ↦ ((constantSheafAdj J (Type (max w u v)) hT).homEquiv I s.pt).symm
      (↾fun i ↦ J.uliftSheafifiedRepresentableHomEquiv s.pt T (s.inj i)))
    (fun _ _ ↦ sorry) (fun _ _ _ ↦ sorry)

/-- A disjoint cover by copies of a terminal object represents the constant sheaf
of labels. Both directions are obtained from specified coproduct descent maps. -/
def constantSheafIsoOfDisjointCover (c : Cofan fun _ : I ↦ T)
    (hcov : Sieve.ofArrows _ c.inj ∈ J c.pt) [∀ i, Mono (c.inj i)]
    (hdisj : ∀ {i j : I}, i ≠ j → ∀ {Y : C} (a : Y ⟶ T) (b : Y ⟶ T),
      a ≫ c.inj i = b ≫ c.inj j → (⊥ : Sieve Y) ∈ J Y) :
    (constantSheaf J (Type (max w u v))).obj I ≅ J.uliftSheafifiedRepresentable.{w} c.pt :=
  (J.isColimitConstantSheafCofan hT I).coconePointUniqueUpToIso
    (J.isColimitSheafifiedRepresentableCofan c hcov hdisj)

/-- Each represented branch maps back to its own constant label. -/
theorem constantSheafIsoOfDisjointCover_inv_inclusion
    (c : Cofan fun _ : I ↦ T)
    (hcov : Sieve.ofArrows _ c.inj ∈ J c.pt) [∀ i, Mono (c.inj i)]
    (hdisj : ∀ {i j : I}, i ≠ j → ∀ {Y : C} (a : Y ⟶ T) (b : Y ⟶ T),
      a ≫ c.inj i = b ≫ c.inj j → (⊥ : Sieve Y) ∈ J Y) (i : I) :
    J.uliftSheafifiedRepresentableMap (c.inj i) ≫
      (J.constantSheafIsoOfDisjointCover hT I c hcov hdisj).inv =
        (J.constantSheafCofan (T := T) I).inj i := sorry

/-- The forward comparison sends a constant label to its represented branch. -/
theorem constantSheafIsoOfDisjointCover_hom_inclusion
    (c : Cofan fun _ : I ↦ T)
    (hcov : Sieve.ofArrows _ c.inj ∈ J c.pt) [∀ i, Mono (c.inj i)]
    (hdisj : ∀ {i j : I}, i ≠ j → ∀ {Y : C} (a : Y ⟶ T) (b : Y ⟶ T),
      a ≫ c.inj i = b ≫ c.inj j → (⊥ : Sieve Y) ∈ J Y) (i : I) :
    (J.constantSheafCofan (T := T) I).inj i ≫
      (J.constantSheafIsoOfDisjointCover hT I c hcov hdisj).hom =
        J.uliftSheafifiedRepresentableMap (c.inj i) := sorry

end Constant

end CategoryTheory.GrothendieckTopology
