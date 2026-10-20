module

public import Mathlib.AlgebraicGeometry.FunctionField
public import Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap
public import Mathlib.Data.List.TFAE
import Mathlib.Tactic.CrossRefAttribute

/-!
# Dominant morphisms between integral schemes

For a morphism of integral schemes, dominance is equivalent to mapping the generic point to the
generic point. This file relates that condition to injectivity on affine sections and on stalks.
-/

@[expose] public section

open AlgebraicGeometry TopologicalSpace CategoryTheory

universe u

namespace AlgebraicGeometry

/-- A nonempty affine open of a scheme. -/
abbrev NonemptyAffineOpen (X : Scheme.{u}) : Type _ :=
  { U : X.affineOpens // Set.Nonempty (U : Set X) }

/-- A morphism of integral schemes is dominant if and only if it maps the generic point of its
source to the generic point of its target. -/
theorem isDominant_iff_map_genericPoint_eq
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsIntegral X] [IsIntegral Y] :
    IsDominant f ↔ f (genericPoint X) = genericPoint Y := by
  constructor
  · intro hf
    have hclosure : closure (Set.range f) = Set.univ :=
      denseRange_iff_closure_range.mp ((isDominant_iff f).mp hf)
    have hgen : IsGenericPoint (f (genericPoint X)) (Set.univ : Set Y) := by
      simpa [Set.image_univ, hclosure] using
        (genericPoint_spec X).image f.continuous
    exact hgen.eq (genericPoint_spec Y)
  · intro hgeneric
    rw [isDominant_iff, denseRange_iff_closure_range]
    apply Set.eq_univ_of_forall
    intro y
    have hη : genericPoint Y ∈ closure (Set.range f) :=
      subset_closure ⟨genericPoint X, hgeneric⟩
    exact ((genericPoint_spec Y).specializes trivial).mem_closed isClosed_closure hη

/-- For nonempty affine opens in integral schemes, the induced map on sections is injective if
and only if the morphism maps generic point to generic point. -/
theorem appLE_injective_iff_map_genericPoint_eq
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsIntegral X] [IsIntegral Y]
    (U : X.Opens) (hU : IsAffineOpen U) [Nonempty U]
    (V : Y.Opens) (hV : IsAffineOpen V) [Nonempty V]
    (e : U ≤ f ⁻¹ᵁ V) :
    Function.Injective (f.appLE V U e).hom ↔
      f (genericPoint X) = genericPoint Y := by
  have hηX : genericPoint X ∈ U :=
    ((genericPoint_spec X).mem_open_set_iff U.isOpen).mpr (by
      simpa using (show Nonempty U from inferInstance))
  have hηY : genericPoint Y ∈ V :=
    ((genericPoint_spec Y).mem_open_set_iff V.isOpen).mpr (by
      simpa using (show Nonempty V from inferInstance))
  have hsource :
      hU.primeIdealOf ⟨genericPoint X, hηX⟩ = ⊥ := by
    rw [hU.primeIdealOf_genericPoint, genericPoint_eq_bot_of_affine]
  have htarget :
      hV.primeIdealOf ⟨genericPoint Y, hηY⟩ = ⊥ := by
    rw [hV.primeIdealOf_genericPoint, genericPoint_eq_bot_of_affine]
  have hsourceIdeal :
      (hU.primeIdealOf ⟨genericPoint X, hηX⟩).asIdeal = ⊥ := by
    simpa using congrArg PrimeSpectrum.asIdeal hsource
  have htargetIdeal :
      (hV.primeIdealOf ⟨genericPoint Y, hηY⟩).asIdeal = ⊥ := by
    simpa using congrArg PrimeSpectrum.asIdeal htarget
  have hcomap :=
    IsAffineOpen.comap_primeIdealOf_appLE V hV U hU e hηX
  have hcomapIdeal :
      Ideal.comap (f.appLE V U e).hom
          (hU.primeIdealOf ⟨genericPoint X, hηX⟩).asIdeal =
        (hV.primeIdealOf ⟨f (genericPoint X), e hηX⟩).asIdeal := by
    simpa using congrArg PrimeSpectrum.asIdeal hcomap
  constructor
  · intro hinjective
    have hker : Ideal.comap (f.appLE V U e).hom ⊥ = ⊥ := by
      rw [← RingHom.ker_eq_comap_bot, ← RingHom.injective_iff_ker_eq_bot]
      exact hinjective
    have himageIdeal :
        (hV.primeIdealOf ⟨f (genericPoint X), e hηX⟩).asIdeal = ⊥ := by
      rw [← hcomapIdeal, hsourceIdeal, hker]
    have hpoint :
        hV.primeIdealOf ⟨f (genericPoint X), e hηX⟩ =
          hV.primeIdealOf ⟨genericPoint Y, hηY⟩ :=
      PrimeSpectrum.ext (himageIdeal.trans htargetIdeal.symm)
    have hfrom := congrArg hV.fromSpec hpoint
    simpa only [hV.fromSpec_primeIdealOf] using hfrom
  · intro hgeneric
    rw [RingHom.injective_iff_ker_eq_bot, RingHom.ker_eq_comap_bot]
    rw [← hsourceIdeal, hcomapIdeal]
    have hpoint :
        (⟨f (genericPoint X), e hηX⟩ : V) =
          ⟨genericPoint Y, hηY⟩ :=
      Subtype.ext hgeneric
    rw [hpoint, htargetIdeal]

/-- Injectivity of a stalk map implies injectivity of the induced section map on any pair of
neighbourhoods to which the morphism restricts. -/
theorem appLE_injective_of_stalkMap_injective
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsIntegral X] [IsIntegral Y]
    (x : X) (U : X.Opens) (hxU : x ∈ U)
    (V : Y.Opens) (hxV : f x ∈ V) (e : U ≤ f ⁻¹ᵁ V)
    (hinjective : Function.Injective (f.stalkMap x).hom) :
    Function.Injective (f.appLE V U e).hom := by
  have hcomm :
      f.appLE V U e ≫ X.presheaf.germ U x hxU =
        Y.presheaf.germ V (f x) hxV ≫ f.stalkMap x := by
    simp only [Scheme.Hom.appLE, Category.assoc, X.presheaf.germ_res',
      f.germ_stalkMap]
  rw [injective_iff_map_eq_zero]
  intro a ha
  apply (germ_injective_of_isIntegral Y (f x) hxV)
  apply hinjective
  rw [← ConcreteCategory.comp_apply, ← ConcreteCategory.comp_apply, ← hcomm]
  rw [ConcreteCategory.comp_apply, ha, map_zero]
  simp

/-- Injectivity of one induced section map around a point implies injectivity of the stalk map at
that point. -/
theorem stalkMap_injective_of_appLE_injective
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsIntegral X] [IsIntegral Y]
    (x : X) (U : X.Opens) (hxU : x ∈ U)
    (V : Y.Opens) (hV : IsAffineOpen V) (hxV : f x ∈ V)
    (e : U ≤ f ⁻¹ᵁ V)
    (hinjective : Function.Injective (f.appLE V U e).hom) :
    Function.Injective (f.stalkMap x).hom := by
  have hcomm :
      f.appLE V U e ≫ X.presheaf.germ U x hxU =
        Y.presheaf.germ V (f x) hxV ≫ f.stalkMap x := by
    simp only [Scheme.Hom.appLE, Category.assoc, X.presheaf.germ_res',
      f.germ_stalkMap]
  apply hV.stalkMap_injective f x hxV
  intro g hg
  have happ :
      (f.appLE V U e).hom g = 0 := by
    apply germ_injective_of_isIntegral X x hxU
    rw [← ConcreteCategory.comp_apply, hcomm]
    rw [ConcreteCategory.comp_apply, hg, map_zero]
  have hg0 : g = 0 :=
    ((injective_iff_map_eq_zero (f.appLE V U e).hom).mp hinjective) g happ
  rw [hg0, map_zero]

/-- At every point of the source, injectivity of the stalk map is equivalent to mapping generic
point to generic point. -/
theorem stalkMap_injective_iff_map_genericPoint_eq
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsIntegral X] [IsIntegral Y] (x : X) :
    Function.Injective (f.stalkMap x).hom ↔
      f (genericPoint X) = genericPoint Y := by
  obtain ⟨_, ⟨V, hV, rfl⟩, hxV, -⟩ :=
    Y.isBasis_affineOpens.exists_subset_of_mem_open
      (Set.mem_univ (f x)) isOpen_univ
  obtain ⟨_, ⟨U, hU, rfl⟩, hxU, hUV⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open
      hxV (f ⁻¹ᵁ V).isOpen
  -- Local instance justification (proof-local temporary data): the exhibited point `x` supplies the nonemptiness of `U` required by the affine generic-point criterion.
  letI : Nonempty U := ⟨⟨x, hxU⟩⟩
  -- Local instance justification (proof-local temporary data): the exhibited point `f x` supplies the nonemptiness of `V` required by the affine generic-point criterion.
  letI : Nonempty V := ⟨⟨f x, hxV⟩⟩
  constructor
  · intro hstalk
    exact (appLE_injective_iff_map_genericPoint_eq f U hU V hV hUV).mp
      (appLE_injective_of_stalkMap_injective f x U hxU V hxV hUV hstalk)
  · intro hgeneric
    exact stalkMap_injective_of_appLE_injective f x U hxU V hV hxV hUV
      ((appLE_injective_iff_map_genericPoint_eq f U hU V hV hUV).mpr hgeneric)

/-- For a morphism of integral schemes, dominance, preservation of generic points, injectivity on
some or all pairs of nonempty affine opens, and injectivity on some or all stalks are equivalent. -/
@[stacks 0CC1]
theorem isDominant_tfae_of_isIntegral
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsIntegral X] [IsIntegral Y] :
    List.TFAE
      [ IsDominant f
      , f (genericPoint X) = genericPoint Y
      , ∃ U : NonemptyAffineOpen X, ∃ V : NonemptyAffineOpen Y,
            ∃ e :
                ((U.1 : X.affineOpens) : X.Opens) ≤
                  (TopologicalSpace.Opens.map f.base).obj ((V.1 : Y.affineOpens) : Y.Opens),
              Function.Injective
                (CommRingCat.Hom.hom
                  (Scheme.Hom.appLE f ((V.1 : Y.affineOpens) : Y.Opens)
                    ((U.1 : X.affineOpens) : X.Opens) e))
      , ∀ U : NonemptyAffineOpen X, ∀ V : NonemptyAffineOpen Y,
            ∀ e :
                ((U.1 : X.affineOpens) : X.Opens) ≤
                  (TopologicalSpace.Opens.map f.base).obj ((V.1 : Y.affineOpens) : Y.Opens),
              Function.Injective
                (CommRingCat.Hom.hom
                  (Scheme.Hom.appLE f ((V.1 : Y.affineOpens) : Y.Opens)
                    ((U.1 : X.affineOpens) : X.Opens) e))
      , ∃ x : X, Function.Injective (CommRingCat.Hom.hom (Scheme.Hom.stalkMap f x))
      , ∀ x : X, Function.Injective (CommRingCat.Hom.hom (Scheme.Hom.stalkMap f x))
      ] := by
  tfae_have 1 ↔ 2 := isDominant_iff_map_genericPoint_eq f
  tfae_have 2 → 4 := by
    intro hgeneric U V e
    -- Local instance justification (proof-local temporary data): the stored nonempty-affine witness in `U` supplies the temporary instance required by the affine generic-point criterion.
    letI : Nonempty (U.1 : X.Opens) := U.2.to_subtype
    -- Local instance justification (proof-local temporary data): the stored nonempty-affine witness in `V` supplies the temporary instance required by the affine generic-point criterion.
    letI : Nonempty (V.1 : Y.Opens) := V.2.to_subtype
    exact (appLE_injective_iff_map_genericPoint_eq f (U.1 : X.Opens) U.1.2
      (V.1 : Y.Opens) V.1.2 e).mpr hgeneric
  tfae_have 4 → 3 := by
    intro hforall
    obtain ⟨_, ⟨V, hV, rfl⟩, hxV, -⟩ :=
      Y.isBasis_affineOpens.exists_subset_of_mem_open
        (Set.mem_univ (f (genericPoint X))) isOpen_univ
    obtain ⟨_, ⟨U, hU, rfl⟩, hxU, hUV⟩ :=
      X.isBasis_affineOpens.exists_subset_of_mem_open
        hxV (f ⁻¹ᵁ V).isOpen
    let U' : NonemptyAffineOpen X :=
      ⟨⟨U, hU⟩, ⟨genericPoint X, hxU⟩⟩
    let V' : NonemptyAffineOpen Y :=
      ⟨⟨V, hV⟩, ⟨f (genericPoint X), hxV⟩⟩
    exact ⟨U', V', hUV, hforall U' V' hUV⟩
  tfae_have 3 → 2 := by
    rintro ⟨U, V, e, hinjective⟩
    -- Local instance justification (proof-local temporary data): the stored nonempty-affine witness in `U` supplies the temporary instance required by the affine generic-point criterion.
    letI : Nonempty (U.1 : X.Opens) := U.2.to_subtype
    -- Local instance justification (proof-local temporary data): the stored nonempty-affine witness in `V` supplies the temporary instance required by the affine generic-point criterion.
    letI : Nonempty (V.1 : Y.Opens) := V.2.to_subtype
    exact (appLE_injective_iff_map_genericPoint_eq f (U.1 : X.Opens) U.1.2
      (V.1 : Y.Opens) V.1.2 e).mp hinjective
  tfae_have 2 → 6 := by
    intro hgeneric x
    exact (stalkMap_injective_iff_map_genericPoint_eq f x).mpr hgeneric
  tfae_have 6 → 5 := fun h ↦ ⟨genericPoint X, h (genericPoint X)⟩
  tfae_have 5 → 2 := by
    rintro ⟨x, hx⟩
    exact (stalkMap_injective_iff_map_genericPoint_eq f x).mp hx
  tfae_finish

end AlgebraicGeometry
