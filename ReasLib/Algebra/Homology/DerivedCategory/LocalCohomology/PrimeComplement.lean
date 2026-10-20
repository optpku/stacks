module

public import ReasLib.Algebra.Homology.DerivedCategory.LocalCohomology.SubmonoidColimit

@[expose] public section

noncomputable section

universe u

open CategoryTheory Limits

namespace CategoryTheory.DerivedCategory.LocalCohomology

variable {A : Type u} [CommRing A]

/-- The support ideal obtained by adjoining the principal ideal of an element outside a prime ideal. -/
abbrev primeComplementSupport (I p : Ideal A) [p.IsPrime]
    (f : p.primeCompl.Divisibility) : Ideal A :=
  I ⊔ Ideal.span {(f : A)}

/-- Divisibility in the complement of a prime reverses inclusion of the associated support ideals. -/
theorem primeComplementSupport_antitone (I : Ideal A) {p : Ideal A} [p.IsPrime]
    {f g : p.primeCompl.Divisibility} (hfg : f ≤ g) :
    primeComplementSupport I p g ≤ primeComplementSupport I p f := sorry

/-- The degree-`i` local-cohomology module supported on the zero locus of the support ideal associated to `f`. -/
noncomputable abbrev primeComplementStage (I : Ideal A) {p : Ideal A} [p.IsPrime]
    (M : ModuleCat A)
    (RΓ : (f : p.primeCompl.Divisibility) →
      DerivedCategory (ModuleCat A) ⥤ IdealPowerTorsion (primeComplementSupport I p f))
    (i : ℤ) (f : p.primeCompl.Divisibility) : ModuleCat A :=
  supportedCohomology (primeComplementSupport I p f) (RΓ f) M i

/-- The local-cohomology transition map induced by divisibility in the complement of a prime. -/
noncomputable def primeComplementTransition (I : Ideal A) {p : Ideal A} [p.IsPrime]
    (M : ModuleCat A)
    (RΓ : (f : p.primeCompl.Divisibility) →
      DerivedCategory (ModuleCat A) ⥤ IdealPowerTorsion (primeComplementSupport I p f))
    (hRΓ : ∀ f : p.primeCompl.Divisibility,
      IdealPowerTorsion.inclusion (primeComplementSupport I p f) ⊣ RΓ f)
    (i : ℤ) {f g : p.primeCompl.Divisibility} (e : f ⟶ g) :
    primeComplementStage I M RΓ i f ⟶ primeComplementStage I M RΓ i g :=
  (DerivedCategory.homologyFunctor (ModuleCat A) i).map
    (supportRestrictionAmbientApp (primeComplementSupport_antitone I (leOfHom e))
      (RΓ g) (RΓ f) (hRΓ g) (hRΓ f) (ModuleCat.single0 M))

/-- The transition map associated to an identity morphism is an identity morphism. -/
theorem primeComplementTransition_id (I : Ideal A) {p : Ideal A} [p.IsPrime]
    (M : ModuleCat A)
    (RΓ : (f : p.primeCompl.Divisibility) →
      DerivedCategory (ModuleCat A) ⥤ IdealPowerTorsion (primeComplementSupport I p f))
    (hRΓ : ∀ f : p.primeCompl.Divisibility,
      IdealPowerTorsion.inclusion (primeComplementSupport I p f) ⊣ RΓ f)
    (i : ℤ) (f : p.primeCompl.Divisibility) :
    primeComplementTransition I M RΓ hRΓ i (𝟙 f) = 𝟙 _ := sorry

/-- The prime-complement transition maps respect composition. -/
theorem primeComplementTransition_comp (I : Ideal A) {p : Ideal A} [p.IsPrime]
    (M : ModuleCat A)
    (RΓ : (f : p.primeCompl.Divisibility) →
      DerivedCategory (ModuleCat A) ⥤ IdealPowerTorsion (primeComplementSupport I p f))
    (hRΓ : ∀ f : p.primeCompl.Divisibility,
      IdealPowerTorsion.inclusion (primeComplementSupport I p f) ⊣ RΓ f)
    (i : ℤ) {f g h : p.primeCompl.Divisibility} (e : f ⟶ g) (e' : g ⟶ h) :
    primeComplementTransition I M RΓ hRΓ i (e ≫ e') =
      primeComplementTransition I M RΓ hRΓ i e ≫
        primeComplementTransition I M RΓ hRΓ i e' := sorry

/-- The functor of degree-`i` local-cohomology modules supported on the prime-complement family. -/
noncomputable def primeComplementDiagram (I : Ideal A) {p : Ideal A} [p.IsPrime]
    (M : ModuleCat A)
    (RΓ : (f : p.primeCompl.Divisibility) →
      DerivedCategory (ModuleCat A) ⥤ IdealPowerTorsion (primeComplementSupport I p f))
    (hRΓ : ∀ f : p.primeCompl.Divisibility,
      IdealPowerTorsion.inclusion (primeComplementSupport I p f) ⊣ RΓ f)
    (i : ℤ) : p.primeCompl.Divisibility ⥤ ModuleCat A where
  obj f := primeComplementStage I M RΓ i f
  map e := primeComplementTransition I M RΓ hRΓ i e
  map_id f := primeComplementTransition_id I M RΓ hRΓ i f
  map_comp e e' := primeComplementTransition_comp I M RΓ hRΓ i e e'

/-- The canonical morphism from an `(I, f)`-supported local-cohomology stage to the `I`-supported stage. -/
noncomputable def primeComplementStageMap (I : Ideal A) {p : Ideal A} [p.IsPrime]
    (M : ModuleCat A)
    (RΓI : DerivedCategory (ModuleCat A) ⥤ IdealPowerTorsion I)
    (RΓ : (f : p.primeCompl.Divisibility) →
      DerivedCategory (ModuleCat A) ⥤ IdealPowerTorsion (primeComplementSupport I p f))
    (hRΓI : IdealPowerTorsion.inclusion I ⊣ RΓI)
    (hRΓ : ∀ f : p.primeCompl.Divisibility,
      IdealPowerTorsion.inclusion (primeComplementSupport I p f) ⊣ RΓ f)
    (i : ℤ) (f : p.primeCompl.Divisibility) :
    primeComplementStage I M RΓ i f ⟶ supportedCohomology I RΓI M i :=
  (DerivedCategory.homologyFunctor (ModuleCat A) i).map
    (supportRestrictionAmbientApp (le_sup_left : I ≤ primeComplementSupport I p f)
      RΓI (RΓ f) hRΓI (hRΓ f) (ModuleCat.single0 M))

/-- The stage maps to `I`-supported local cohomology satisfy the cocone naturality equation. -/
theorem primeComplementStageMap_naturality (I : Ideal A) {p : Ideal A} [p.IsPrime]
    (M : ModuleCat A)
    (RΓI : DerivedCategory (ModuleCat A) ⥤ IdealPowerTorsion I)
    (RΓ : (f : p.primeCompl.Divisibility) →
      DerivedCategory (ModuleCat A) ⥤ IdealPowerTorsion (primeComplementSupport I p f))
    (hRΓI : IdealPowerTorsion.inclusion I ⊣ RΓI)
    (hRΓ : ∀ f : p.primeCompl.Divisibility,
      IdealPowerTorsion.inclusion (primeComplementSupport I p f) ⊣ RΓ f)
    (i : ℤ) {f g : p.primeCompl.Divisibility} (e : f ⟶ g) :
    (primeComplementDiagram I M RΓ hRΓ i).map e ≫
        primeComplementStageMap I M RΓI RΓ hRΓI hRΓ i g =
      primeComplementStageMap I M RΓI RΓ hRΓI hRΓ i f ≫ 𝟙 _ := sorry

/-- The canonical cocone from the prime-complement diagram to `I`-supported local cohomology. -/
noncomputable def primeComplementCocone (I : Ideal A) {p : Ideal A} [p.IsPrime]
    (M : ModuleCat A)
    (RΓI : DerivedCategory (ModuleCat A) ⥤ IdealPowerTorsion I)
    (RΓ : (f : p.primeCompl.Divisibility) →
      DerivedCategory (ModuleCat A) ⥤ IdealPowerTorsion (primeComplementSupport I p f))
    (hRΓI : IdealPowerTorsion.inclusion I ⊣ RΓI)
    (hRΓ : ∀ f : p.primeCompl.Divisibility,
      IdealPowerTorsion.inclusion (primeComplementSupport I p f) ⊣ RΓ f)
    (i : ℤ) : Cocone (primeComplementDiagram I M RΓ hRΓ i) :=
  Cocone.mk (supportedCohomology I RΓI M i)
    { app := primeComplementStageMap I M RΓI RΓ hRΓI hRΓ i
      naturality := fun {_ _} e ↦
        primeComplementStageMap_naturality I M RΓI RΓ hRΓI hRΓ i e }

/-- The comparison morphism from the prime-complement colimit to `I`-supported local cohomology. -/
noncomputable def primeComplementComparison (I p : Ideal A) [p.IsPrime] (hI : I.FG)
    (M : ModuleCat A) (i : ℤ) (hi : 0 ≤ i)
    (RΓI : DerivedCategory (ModuleCat A) ⥤ IdealPowerTorsion I)
    (RΓ : (f : p.primeCompl.Divisibility) →
      DerivedCategory (ModuleCat A) ⥤ IdealPowerTorsion (primeComplementSupport I p f))
    (hRΓI : IdealPowerTorsion.inclusion I ⊣ RΓI)
    (hRΓ : ∀ f : p.primeCompl.Divisibility,
      IdealPowerTorsion.inclusion (primeComplementSupport I p f) ⊣ RΓ f) :
    colimit (primeComplementDiagram I M RΓ hRΓ i) ⟶ supportedCohomology I RΓI M i :=
  colimit.desc (primeComplementDiagram I M RΓ hRΓ i)
    (primeComplementCocone I M RΓI RΓ hRΓI hRΓ i)

/-- The comparison morphism has range equal to the kernel of localization at the prime. -/
theorem primeComplementComparison_range (I p : Ideal A) [p.IsPrime] (hI : I.FG)
    (M : ModuleCat A) (i : ℤ) (hi : 0 ≤ i)
    (RΓI : DerivedCategory (ModuleCat A) ⥤ IdealPowerTorsion I)
    (RΓ : (f : p.primeCompl.Divisibility) →
      DerivedCategory (ModuleCat A) ⥤ IdealPowerTorsion (primeComplementSupport I p f))
    (hRΓI : IdealPowerTorsion.inclusion I ⊣ RΓI)
    (hRΓ : ∀ f : p.primeCompl.Divisibility,
      IdealPowerTorsion.inclusion (primeComplementSupport I p f) ⊣ RΓ f) :
    (primeComplementComparison I p hI M i hi RΓI RΓ hRΓI hRΓ).hom.range =
      (LocalizedModule.mkLinearMap p.primeCompl (supportedCohomology I RΓI M i)).ker := sorry

/-- Localized vanishing in degree `i - 1` makes the prime-complement comparison injective. -/
theorem primeComplementComparison_injective (I p : Ideal A) [p.IsPrime] (hI : I.FG)
    (M : ModuleCat A) (i : ℤ) (hi : 0 ≤ i)
    (RΓI : DerivedCategory (ModuleCat A) ⥤ IdealPowerTorsion I)
    (RΓ : (f : p.primeCompl.Divisibility) →
      DerivedCategory (ModuleCat A) ⥤ IdealPowerTorsion (primeComplementSupport I p f))
    (hRΓI : IdealPowerTorsion.inclusion I ⊣ RΓI)
    (hRΓ : ∀ f : p.primeCompl.Divisibility,
      IdealPowerTorsion.inclusion (primeComplementSupport I p f) ⊣ RΓ f)
    [Subsingleton (LocalizedModule p.primeCompl
      (supportedCohomology I RΓI M (i - 1)))] :
    Function.Injective (primeComplementComparison I p hI M i hi RΓI RΓ hRΓI hRΓ) := sorry

/-- Localized vanishing in degrees `i - 1` and `i` makes the prime-complement comparison bijective. -/
theorem primeComplementComparison_bijective (I p : Ideal A) [p.IsPrime] (hI : I.FG)
    (M : ModuleCat A) (i : ℤ) (hi : 0 ≤ i)
    (RΓI : DerivedCategory (ModuleCat A) ⥤ IdealPowerTorsion I)
    (RΓ : (f : p.primeCompl.Divisibility) →
      DerivedCategory (ModuleCat A) ⥤ IdealPowerTorsion (primeComplementSupport I p f))
    (hRΓI : IdealPowerTorsion.inclusion I ⊣ RΓI)
    (hRΓ : ∀ f : p.primeCompl.Divisibility,
      IdealPowerTorsion.inclusion (primeComplementSupport I p f) ⊣ RΓ f)
    [Subsingleton (LocalizedModule p.primeCompl
      (supportedCohomology I RΓI M (i - 1)))]
    [Subsingleton (LocalizedModule p.primeCompl (supportedCohomology I RΓI M i))] :
    Function.Bijective (primeComplementComparison I p hI M i hi RΓI RΓ hRΓI hRΓ) := sorry

end CategoryTheory.DerivedCategory.LocalCohomology
