module

public import Mathlib.Algebra.Category.ModuleCat.Basic
public import Mathlib.Algebra.Homology.Augment
public import ReasLib.Algebra.Module.LocalizedModule.Away.Map

/-!
# Product Cech complexes of principal module localizations

This file constructs the product-indexed Cech cochain complex associated to a finite family of
principal localizations. Its terms are indexed by ordered tuples, and its differentials are the
alternating sums of the restriction maps obtained by deleting one tuple coordinate.
-/

@[expose] public section

noncomputable section

open CategoryTheory

universe u v

namespace LocalizedModule.Away.Cech.Product

variable {R : Type u} [CommRing R]
variable {r : ℕ}

/-- The product of the entries of `f` selected by an ordered finite tuple. -/
def denominator (f : Fin r → R) {n : ℕ} (i : Fin n → Fin r) : R :=
  ∏ j, f (i j)

/-- The denominator attached to the tuple obtained by deleting one coordinate divides the
denominator of the original tuple. -/
theorem denominator_delete_dvd (f : Fin r → R) (p : ℕ)
    (i : Fin (p + 2) → Fin r) (k : Fin (p + 2)) :
    denominator f (fun j ↦ i (k.succAbove j)) ∣ denominator f i := by
  refine ⟨f (i k), ?_⟩
  rw [denominator, denominator, Fin.prod_univ_succAbove]
  exact mul_comm _ _

/-- The degree-`p` product of the module localizations indexed by ordered `(p + 1)`-tuples. -/
def term (f : Fin r → R) (M : Type (max u v)) [AddCommGroup M] [Module R M]
    (p : ℕ) : ModuleCat.{max u v} R :=
  ModuleCat.of R
    (∀ i : Fin (p + 1) → Fin r, LocalizedModule.Away (denominator f i) M)

/-- The Cech coface obtained by deleting one tuple coordinate and restricting along the resulting
divisibility of principal denominators. -/
noncomputable def coface (f : Fin r → R) (M : Type (max u v))
    [AddCommGroup M] [Module R M] (p : ℕ) (k : Fin (p + 2)) :
    term f M p ⟶ term f M (p + 1) :=
  ModuleCat.ofHom (LinearMap.pi fun i ↦
    (LocalizedModule.Away.mapOfDvd
      (denominator f (fun j ↦ i (k.succAbove j))) (denominator f i)
      (denominator_delete_dvd f p i k)).comp
        (LinearMap.proj (fun j ↦ i (k.succAbove j))))

/-- Evaluation of a Cech coface is restriction of the component obtained by deleting its chosen
coordinate. -/
theorem coface_apply (f : Fin r → R) (M : Type (max u v))
    [AddCommGroup M] [Module R M] (p : ℕ) (k : Fin (p + 2))
    (x : term f M p) (i : Fin (p + 2) → Fin r) :
    (coface f M p k).hom x i =
      LocalizedModule.Away.mapOfDvd
        (denominator f (fun j ↦ i (k.succAbove j))) (denominator f i)
        (denominator_delete_dvd f p i k) (x (fun j ↦ i (k.succAbove j))) := sorry

/-- The alternating sum of the Cech cofaces in degree `p`. -/
noncomputable def differential (f : Fin r → R) (M : Type (max u v))
    [AddCommGroup M] [Module R M] (p : ℕ) :
    term f M p ⟶ term f M (p + 1) :=
  ∑ k : Fin (p + 2), if Even k.val then coface f M p k else -coface f M p k

/-- Evaluation of the Cech differential is the alternating sum of the corresponding restriction
maps. -/
theorem differential_apply (f : Fin r → R) (M : Type (max u v))
    [AddCommGroup M] [Module R M] (p : ℕ) (x : term f M p)
    (i : Fin (p + 2) → Fin r) :
    (differential f M p).hom x i =
      ∑ k : Fin (p + 2), if Even k.val then
        LocalizedModule.Away.mapOfDvd
          (denominator f (fun j ↦ i (k.succAbove j))) (denominator f i)
          (denominator_delete_dvd f p i k) (x (fun j ↦ i (k.succAbove j)))
      else
        -LocalizedModule.Away.mapOfDvd
          (denominator f (fun j ↦ i (k.succAbove j))) (denominator f i)
          (denominator_delete_dvd f p i k) (x (fun j ↦ i (k.succAbove j))) := sorry

/-- Consecutive alternating Cech differentials compose to zero. -/
theorem differential_comp (f : Fin r → R) (M : Type (max u v))
    [AddCommGroup M] [Module R M] (p : ℕ) :
    differential f M p ≫ differential f M (p + 1) = 0 := sorry

/-- The product-indexed Cech cochain complex of a finite family of principal localizations. -/
noncomputable def complex (f : Fin r → R) (M : Type (max u v))
    [AddCommGroup M] [Module R M] : CochainComplex (ModuleCat.{max u v} R) ℕ :=
  CochainComplex.of (term f M) (differential f M) (differential_comp f M)

/-- The object in degree `p` of the product-indexed Cech complex is its explicit localization
product. -/
theorem complex_X (f : Fin r → R) (M : Type (max u v))
    [AddCommGroup M] [Module R M] (p : ℕ) :
    (complex f M).X p = term f M p := sorry

/-- The differential from degree `p` to degree `p + 1` in the product-indexed Cech complex is the
explicit alternating restriction map. -/
theorem complex_d (f : Fin r → R) (M : Type (max u v))
    [AddCommGroup M] [Module R M] (p : ℕ) :
    (complex f M).d p (p + 1) = differential f M p := sorry

/-- The canonical map from a module to the product of its one-element principal localizations. -/
noncomputable def augmentationMap (f : Fin r → R) (M : Type (max u v))
    [AddCommGroup M] [Module R M] : ModuleCat.of R M ⟶ term f M 0 :=
  ModuleCat.ofHom (LinearMap.pi fun i ↦
    LocalizedModule.mkLinearMap (Submonoid.powers (denominator f i)) M)

/-- The localization-family map followed by the first alternating Cech differential is zero. -/
theorem augmentationMap_comp_differential (f : Fin r → R)
    (M : Type (max u v)) [AddCommGroup M] [Module R M] :
    augmentationMap f M ≫ differential f M 0 = 0 := sorry

/-- The canonical augmentation from the module concentrated in degree zero to its product-indexed
Cech complex. -/
noncomputable def augmentation (f : Fin r → R) (M : Type (max u v))
    [AddCommGroup M] [Module R M] :
    (CochainComplex.single₀ (ModuleCat.{max u v} R)).obj (ModuleCat.of R M) ⟶ complex f M :=
  (CochainComplex.fromSingle₀Equiv (complex f M) (ModuleCat.of R M)).symm
    ⟨augmentationMap f M, augmentationMap_comp_differential f M⟩

/-- The extended product-indexed Cech complex, with the original module in degree zero. -/
noncomputable def extended (f : Fin r → R) (M : Type (max u v))
    [AddCommGroup M] [Module R M] : CochainComplex (ModuleCat.{max u v} R) ℕ :=
  CochainComplex.fromSingle₀AsComplex (complex f M) (ModuleCat.of R M) (augmentation f M)

/-- Degree zero of the extended product-indexed Cech complex is the original module. -/
theorem extended_X_zero (f : Fin r → R) (M : Type (max u v))
    [AddCommGroup M] [Module R M] :
    (extended f M).X 0 = ModuleCat.of R M := sorry

/-- Degree `p + 1` of the extended product-indexed Cech complex is the explicit degree-`p`
localization product. -/
theorem extended_X_succ (f : Fin r → R) (M : Type (max u v))
    [AddCommGroup M] [Module R M] (p : ℕ) :
    (extended f M).X (p + 1) = term f M p := sorry

/-- The differential from degree zero to degree one of the extended complex is the canonical
localization-family map. -/
theorem extended_d_zero_one (f : Fin r → R) (M : Type (max u v))
    [AddCommGroup M] [Module R M] :
    (extended f M).d 0 1 = augmentationMap f M := sorry

/-- The differential from degree `p + 1` to degree `p + 2` of the extended complex is the
degree-`p` alternating Cech differential. -/
theorem extended_d_succ_succ (f : Fin r → R) (M : Type (max u v))
    [AddCommGroup M] [Module R M] (p : ℕ) :
    (extended f M).d (p + 1) (p + 2) = differential f M p := sorry

end LocalizedModule.Away.Cech.Product

end
