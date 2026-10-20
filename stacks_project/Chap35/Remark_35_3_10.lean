module

import ReasLib.Algebra.Module.LocalizedModule.Away.Cech.Cohomology
import ReasLib.Algebra.Module.LocalizedModule.Away.Cech.Product
import ReasLib.AlgebraicGeometry.Scheme.Module.Cech.StandardCover
import ReasLib.AlgebraicGeometry.Scheme.Spec.BasicOpen.FaithfullyFlat
import StacksCheckRecall

@[expose] public section

universe u v

/- Remark 35.3.10 (1): if `f : Fin r → R` generates the unit ideal, then the
map `R →+* ∀ i, Localization.Away (f i)` is faithfully flat. -/
@[stacks 023O] #check
  (AlgebraicGeometry.Spec.BasicOpenUnion.localizationProductMap_faithfullyFlat :
    ∀ {R : Type u} [CommRing R] {r : ℕ} (f : Fin r → R),
      Ideal.span (Set.range f) = ⊤ →
        (AlgebraicGeometry.Spec.BasicOpenUnion.localizationProductMap f).FaithfullyFlat)

/- Remark 35.3.10 (2): the underlying `R`-module view of the source's degree-`p`
ring is `ModuleCat.of R (∀ i : Fin (p + 1) → Fin r,
LocalizedModule.Away (Product.denominator f i) R)`. -/
@[stacks 023O] #check
  (LocalizedModule.Away.Cech.Product.complex_X :
    ∀ {R : Type u} [CommRing R] {r : ℕ} (f : Fin r → R)
      (M : Type (max u v)) [AddCommGroup M] [Module R M] (p : ℕ),
      (LocalizedModule.Away.Cech.Product.complex f M).X p =
        ModuleCat.of R
          (∀ i : Fin (p + 1) → Fin r,
            LocalizedModule.Away
              (LocalizedModule.Away.Cech.Product.denominator f i) M))

/- Remark 35.3.10 (3): the augmented principal-localization Čech complex has zero
cohomology in every degree when the family generates the unit ideal. -/
@[stacks 023O] #check
  (LocalizedModule.Away.Cech.Alternating.Cohomology.isZero_of_span_eq_top :
    ∀ {R : Type u} [CommRing R]
      {M : Type (max u v)} [AddCommGroup M] [Module R M] {r : ℕ}
      (f : Fin r → R), Ideal.span (Set.range f) = ⊤ → ∀ q : ℕ,
        CategoryTheory.Limits.IsZero
          ((LocalizedModule.Away.Cech.Alternating.extended f M).homology q))

/- Remark 35.3.10 (4): quasi-coherent modules on affine opens are Čech-acyclic for
standard distinguished-open covers. -/
@[stacks 023O] #check
  (AlgebraicGeometry.Scheme.StandardZariskiCover.OnAffineOpen.isCechAcyclicFamily :
    ∀ {X : AlgebraicGeometry.Scheme.{u}} {U : X.affineOpens}
      (𝒰 : AlgebraicGeometry.Scheme.StandardZariskiCover.OnAffineOpen.{u, u} X U)
      (ℱ : X.Modules) [ℱ.IsQuasicoherent], ∀ p : ℕ, 0 < p →
        CategoryTheory.Limits.IsZero
          (AlgebraicGeometry.RingedSpace.moduleCechCohomology 𝒰.opens ℱ p))
