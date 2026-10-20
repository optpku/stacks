module

public import ReasLib.CategoryTheory.Functor.OfSequence.Colimit
public import ReasLib.CategoryTheory.Pro.HomColimit
public import ReasLib.CategoryTheory.Pro.Sequential.Realization

/-!
# Diagonalization of sequential pro-systems

This file constructs a diagonal inverse system from an inverse sequence of sequential
pro-morphism representatives and compares its Hom-colimit with the corresponding iterated
Hom-colimit.
-/

@[expose] public section

open CategoryTheory Limits Opposite
open scoped CategoryTheory

noncomputable section

universe u v

namespace CategoryTheory.Pro.SequentialHom

variable {C : Type u} [Category.{v} C]

/-- The stage selected in the `k`-th row by successively applying the first `k`
reindexing functions, starting at `k + 1`. -/
def diagonalIndex {M : ℕ → ℕᵒᵖ ⥤ C}
    (r : ∀ k, Pro.SequentialHom (M (k + 1)) (M k)) (k : ℕ) : ℕ :=
  (List.range k).foldl (fun n i ↦ (r i).reindex n) (k + 1)

/-- The source stage selected for the next diagonal arrow dominates the stage needed by its
sequential representative. -/
theorem reindex_diagonalIndex_le_succ {M : ℕ → ℕᵒᵖ ⥤ C}
    (r : ∀ k, Pro.SequentialHom (M (k + 1)) (M k)) (k : ℕ) :
    (r k).reindex (diagonalIndex r k) ≤ diagonalIndex r (k + 1) := sorry

/-- The transition from the selected stage in row `k + 1` to the selected stage in row `k`. -/
def diagonalStep (M : ℕ → ℕᵒᵖ ⥤ C)
    (r : ∀ k, Pro.SequentialHom (M (k + 1)) (M k)) (k : ℕ) :
    (M (k + 1)).obj (op (diagonalIndex r (k + 1))) ⟶
      (M k).obj (op (diagonalIndex r k)) :=
  (M (k + 1)).map (homOfLE (reindex_diagonalIndex_le_succ r k)).op ≫
    (r k).hom.app (op (diagonalIndex r k))

/-- The diagonal inverse system obtained from the chosen sequential representatives. -/
def diagonal (M : ℕ → ℕᵒᵖ ⥤ C)
    (r : ∀ k, Pro.SequentialHom (M (k + 1)) (M k)) : ℕᵒᵖ ⥤ C :=
  @Functor.ofOpSequence C _
    (fun k ↦ (M k).obj (op (diagonalIndex r k))) (diagonalStep M r)

/-- The objects of the diagonal system are the explicitly selected nested stages. -/
@[simp]
theorem diagonal_obj (M : ℕ → ℕᵒᵖ ⥤ C)
    (r : ∀ k, Pro.SequentialHom (M (k + 1)) (M k)) (k : ℕ) :
    (diagonal M r).obj (op k) = (M k).obj (op (diagonalIndex r k)) := sorry

/-- The successor maps of the diagonal system are its explicit diagonal transitions. -/
@[simp]
theorem diagonal_map_succ (M : ℕ → ℕᵒᵖ ⥤ C)
    (r : ∀ k, Pro.SequentialHom (M (k + 1)) (M k)) (k : ℕ) :
    (diagonal M r).map (homOfLE (Nat.le_succ k)).op = diagonalStep M r k := sorry

/-- The direct system of Hom-colimit functors induced contravariantly by the inverse sequence of
represented pro-object morphisms. -/
def iteratedHomColimit (M : ℕ → ℕᵒᵖ ⥤ C)
    (r : ∀ k, Pro.SequentialHom (M (k + 1)) (M k)) : C ⥤ Type v :=
  colimit (Functor.ofSequence (fun k ↦ Pro.homColimit.map (r k).toHom))

/-- The selected diagonal stage in row `k` maps canonically into the iterated Hom-colimit. -/
def diagonalCoconeApp (M : ℕ → ℕᵒᵖ ⥤ C)
    (r : ∀ k, Pro.SequentialHom (M (k + 1)) (M k)) (k : ℕ) :
    coyoneda.obj (op ((M k).obj (op (diagonalIndex r k)))) ⟶ iteratedHomColimit M r :=
  colimit.ι ((M k).op ⋙ coyoneda) (op (op (diagonalIndex r k))) ≫
    colimit.ι (Functor.ofSequence (fun j ↦ Pro.homColimit.map (r j).toHom)) k

/-- The stage maps into the iterated Hom-colimit respect every transition of the diagonal
system. -/
theorem diagonalCoconeApp_naturality (M : ℕ → ℕᵒᵖ ⥤ C)
    (r : ∀ k, Pro.SequentialHom (M (k + 1)) (M k))
    {i j : (ℕᵒᵖ)ᵒᵖ} (f : i ⟶ j) :
    ((diagonal M r).op ⋙ coyoneda).map f ≫
        diagonalCoconeApp M r j.unop.unop =
      diagonalCoconeApp M r i.unop.unop ≫
        ((Functor.const (ℕᵒᵖ)ᵒᵖ).obj (iteratedHomColimit M r)).map f := sorry

/-- The cocone from the Hom functors of the diagonal stages to the iterated Hom-colimit. -/
def diagonalCocone (M : ℕ → ℕᵒᵖ ⥤ C)
    (r : ∀ k, Pro.SequentialHom (M (k + 1)) (M k)) :
    Cocone ((diagonal M r).op ⋙ coyoneda) :=
  Cocone.mk (iteratedHomColimit M r)
    { app := fun i ↦ diagonalCoconeApp M r i.unop.unop
      naturality := fun _ _ f ↦ diagonalCoconeApp_naturality M r f }

/-- The canonical comparison from the Hom-colimit of the diagonal system to the iterated
Hom-colimit of the rows. -/
def diagonalToIteratedHom (M : ℕ → ℕᵒᵖ ⥤ C)
    (r : ∀ k, Pro.SequentialHom (M (k + 1)) (M k)) :
    Pro.homColimit (diagonal M r) ⟶ iteratedHomColimit M r :=
  colimit.desc ((diagonal M r).op ⋙ coyoneda) (diagonalCocone M r)

/-- The comparison restricts on each diagonal stage to the inner and then outer colimit
inclusions. -/
theorem diagonalToIteratedHom_ι (M : ℕ → ℕᵒᵖ ⥤ C)
    (r : ∀ k, Pro.SequentialHom (M (k + 1)) (M k)) (k : ℕ) :
    colimit.ι ((diagonal M r).op ⋙ coyoneda) (op (op k)) ≫
        diagonalToIteratedHom M r =
      diagonalCoconeApp M r k := sorry

/-- If every chosen monotone representative dominates the identity on indices, the canonical
map from the Hom-colimit of the diagonal system to the iterated Hom-colimit is bijective at
every target object. -/
theorem diagonalToIteratedHom_bijective
    {M : ℕ → ℕᵒᵖ ⥤ C}
    (r : ∀ k, Pro.SequentialHom (M (k + 1)) (M k))
    (h_ge : ∀ k n, n ≤ (r k).reindex n) (N : C) :
    Function.Bijective ((diagonalToIteratedHom M r).app N) := sorry

/-- The pro-object presented by the diagonal inverse system associated to a sequence of
sequential pro-object morphisms. -/
noncomputable def diagonalPro (M : ℕ → ℕᵒᵖ ⥤ C)
    (r : ∀ k, Pro.SequentialHom (M (k + 1)) (M k)) : Pro C :=
  (Pro.lim (C := C) ℕᵒᵖ).obj (diagonal M r)

/-- The realization of `diagonalPro M r` maps naturally to the iterated Hom-colimit of the
rows. -/
noncomputable def diagonalProHomComparison (M : ℕ → ℕᵒᵖ ⥤ C)
    (r : ∀ k, Pro.SequentialHom (M (k + 1)) (M k)) :
    ((Pro.inclusion C).obj (diagonalPro M r)).unop ⟶ iteratedHomColimit M r :=
  (Pro.limInclusionIso (diagonal M r)).hom ≫ diagonalToIteratedHom M r

/-- If every reindexing representative grows its index, the Hom comparison for `diagonalPro M r`
is bijective at every target. -/
theorem diagonalProHomComparison_bijective
    {M : ℕ → ℕᵒᵖ ⥤ C}
    (r : ∀ k, Pro.SequentialHom (M (k + 1)) (M k))
    (h_ge : ∀ k n, n ≤ (r k).reindex n) (N : C) :
    Function.Bijective ((diagonalProHomComparison M r).app N) := sorry

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

private noncomputable def diagonalChain
    {M : ℕ → ℕᵒᵖ ⥤ C}
    (r : ∀ k, Pro.SequentialHom (M (k + 1)) (M k)) (k : ℕ) :
    (n : ℕ) → Pro.SequentialHom (M (k + n)) (M k)
  | 0 => Pro.SequentialHom.id (M k)
  | n + 1 => by
      simpa [Nat.add_assoc] using
        (Pro.SequentialHom.comp (r (k + n)) (diagonalChain r k n))

private theorem diagonalChain_reindex_le
    {M : ℕ → ℕᵒᵖ ⥤ C}
    (r : ∀ k, Pro.SequentialHom (M (k + 1)) (M k))
    (h_ge : ∀ k n, n ≤ (r k).reindex n)
    (k j n : ℕ) (hkj : k ≤ j) (hn : n ≤ j) :
    (diagonalChain r k (j - k)).reindex n ≤ diagonalIndex r j := sorry

private noncomputable def diagonalChainMap
    {M : ℕ → ℕᵒᵖ ⥤ C}
    (r : ∀ k, Pro.SequentialHom (M (k + 1)) (M k))
    (h_ge : ∀ k n, n ≤ (r k).reindex n)
    (k j n : ℕ) (hkj : k ≤ j) (hn : n ≤ j) :
    (M j).obj (op (diagonalIndex r j)) ⟶ (M k).obj (op n) := by
  let q := diagonalChain r k (j - k)
  have hsum : k + (j - k) = j := Nat.add_sub_of_le hkj
  have hstage : q.reindex n ≤ diagonalIndex r j :=
    diagonalChain_reindex_le r h_ge k j n hkj hn
  let f₁ : (M j).obj (op (diagonalIndex r j)) ⟶
      (M (k + (j - k))).obj (op (q.reindex n)) := by
    simpa [hsum] using (M j).map (homOfLE hstage).op
  let f₂ : (M (k + (j - k))).obj (op (q.reindex n)) ⟶ (M k).obj (op n) :=
    q.hom.app (op n)
  simpa [hsum] using (f₁ ≫ f₂)

private noncomputable def diagonalRowToHom
    {M : ℕ → ℕᵒᵖ ⥤ C}
    (r : ∀ k, Pro.SequentialHom (M (k + 1)) (M k))
    (h_ge : ∀ k n, n ≤ (r k).reindex n) (k : ℕ) :
    Pro.homColimit (M k) ⟶ Pro.homColimit (diagonal M r) := by
  let target := Pro.homColimit (diagonal M r)
  let app : ∀ i : (ℕᵒᵖ)ᵒᵖ,
      ((M k).op ⋙ coyoneda).obj i ⟶ target := fun i ↦ by
    let n := i.unop.unop
    let j := max k n
    let hkj : k ≤ j := Nat.le_max_left _ _
    let hn : n ≤ j := Nat.le_max_right _ _
    let sm := diagonalChainMap r h_ge k j n hkj hn
    let source := ((M k).op ⋙ coyoneda).obj i
    exact
      { app := fun N ↦ TypeCat.ofHom (fun f : source.obj N ↦
          let f' : (M k).obj (op n) ⟶ N :=
            (eqToHom (by simp [n]) : (M k).obj (op n) ⟶ (M k).obj i.unop) ≫ f
          (colimit.ι ((diagonal M r).op ⋙ coyoneda)
            (op (op j))).app N (sm ≫ f'))
        naturality := by
          intro X Y f
          simp only [Functor.comp_obj, Category.assoc]
          sorry }
  let c : Cocone ((M k).op ⋙ coyoneda) :=
    Cocone.mk target
      { app := app
        naturality := by
          intro i j f
          sorry }
  exact colimit.desc ((M k).op ⋙ coyoneda) c

private noncomputable def iteratedHomToDiagonal
    {M : ℕ → ℕᵒᵖ ⥤ C}
    (r : ∀ k, Pro.SequentialHom (M (k + 1)) (M k))
    (h_ge : ∀ k n, n ≤ (r k).reindex n) :
    iteratedHomColimit M r ⟶ Pro.homColimit (diagonal M r) :=
  Functor.ofSequence.colimitDesc
    (fun k ↦ Pro.homColimit.map (r k).toHom)
    (fun k ↦ diagonalRowToHom r h_ge k)
    (fun k ↦ by sorry)

private noncomputable def diagonalHomComparisonIso
    {M : ℕ → ℕᵒᵖ ⥤ C}
    (r : ∀ k, Pro.SequentialHom (M (k + 1)) (M k))
    (h_ge : ∀ k n, n ≤ (r k).reindex n) :
    ((Pro.inclusion C).obj (diagonalPro M r)).unop ≅ iteratedHomColimit M r :=
  { hom := diagonalProHomComparison M r
    inv := iteratedHomToDiagonal r h_ge ≫ (Pro.limInclusionIso (diagonal M r)).inv
    hom_inv_id := by sorry
    inv_hom_id := by sorry }

private noncomputable def comparisonIso
    {M : ℕ → ℕᵒᵖ ⥤ C}
    (r : ∀ k, Pro.SequentialHom (M (k + 1)) (M k)) (P : Pro C)
    (comparison : ((Pro.inclusion C).obj P).unop ⟶ iteratedHomColimit M r)
    (h_comparison : ∀ N, Function.Bijective (comparison.app N)) :
    ((Pro.inclusion C).obj P).unop ≅ iteratedHomColimit M r :=
  NatIso.ofComponents
    (fun N ↦ (Equiv.ofBijective (comparison.app N) (h_comparison N)).toIso)
    (by sorry)

/-- The canonical isomorphism from a pro-object `P` to `diagonalPro M r`, determined by a
componentwise-bijective comparison of the realized Hom functor of `P` with the iterated
Hom-colimit. It is the preimage, under the fully faithful realization `Pro.inclusion C`, of the
composite of `comparison` with the inverse of `diagonalProHomComparison M r`. This gives the
unique pro-isomorphism class compatible with the comparison. -/
noncomputable def isoDiagonalPro
    {M : ℕ → ℕᵒᵖ ⥤ C}
    (r : ∀ k, Pro.SequentialHom (M (k + 1)) (M k))
    (h_ge : ∀ k n, n ≤ (r k).reindex n) (P : Pro C)
    (comparison : ((Pro.inclusion C).obj P).unop ⟶ iteratedHomColimit M r)
    (h_comparison : ∀ N, Function.Bijective (comparison.app N)) :
    P ≅ diagonalPro M r :=
  (Pro.inclusion.fullyFaithful.preimageIso
    ((comparisonIso r P comparison h_comparison ≪≫
      (diagonalHomComparisonIso r h_ge).symm).op)).symm

/-- Under the realization, `isoDiagonalPro` intertwines `comparison` with the canonical
comparison `diagonalProHomComparison M r`. -/
theorem isoDiagonalPro_hom_comparison
    {M : ℕ → ℕᵒᵖ ⥤ C}
    (r : ∀ k, Pro.SequentialHom (M (k + 1)) (M k))
    (h_ge : ∀ k n, n ≤ (r k).reindex n) (P : Pro C)
    (comparison : ((Pro.inclusion C).obj P).unop ⟶ iteratedHomColimit M r)
    (h_comparison : ∀ N, Function.Bijective (comparison.app N)) :
    ((Pro.inclusion C).map (isoDiagonalPro r h_ge P comparison h_comparison).hom).unop ≫
        comparison =
      diagonalProHomComparison M r := sorry

end CategoryTheory.Pro.SequentialHom
