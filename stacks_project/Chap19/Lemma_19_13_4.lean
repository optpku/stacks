/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Homology.CochainComplex.KInjective.DerivedProduct
public import ReasLib.CategoryTheory.DerivedCategory.Limit.Coproducts
import StacksCheckRecall

@[expose] public section

/-!
# Coproducts and products in a derived category

The source item is the Grothendieck specialization of the shape-generic derived coproduct API
and the K-injective derived product API.
-/

open CategoryTheory CategoryTheory.Limits

noncomputable section

universe w v u uJ

variable {C : Type u} [Category.{v} C] [Abelian C]
variable [HasDerivedCategory.{w} C] [IsGrothendieckAbelian.{uJ} C]
variable (J : Type uJ)

/- Lemma 19.13.4 (1): `D(C)` has coproducts of every prescribed shape. -/
@[stacks 07D9 "coproduct existence"] #check
  (inferInstance : HasCoproductsOfShape J (DerivedCategory C))

/- Lemma 19.13.4 (2): a termwise coproduct of representative complexes realizes the
corresponding coproduct in `D(C)`. -/
@[stacks 07D9 "termwise coproduct model"] #check
  fun (K : J → CochainComplex C ℤ) ↦
    (DerivedCategory.Coproduct.cofanIsColimit_of_termwise K :
      IsColimit
        (Cofan.mk
          (DerivedCategory.Q.obj (∐ K))
          (fun j ↦ DerivedCategory.Q.map (Sigma.ι K j))))

/- Lemma 19.13.4 (3): `D(C)` has products of every prescribed shape. -/
@[stacks 07D9 "product existence"] #check
  (inferInstance : HasProductsOfShape J (DerivedCategory C))

/- Lemma 19.13.4 (4): a termwise product of K-injective complexes realizes the corresponding
product in `D(C)`. -/
variable (I : J → CochainComplex C ℤ) [∀ j, (I j).IsKInjective]

@[stacks 07D9 "termwise K-injective product model"] #check
  (DerivedCategory.Product.fanIsLimit_of_termwise I :
    IsLimit
      (Fan.mk
        (DerivedCategory.Q.obj (∏ᶜ I))
        (fun j ↦ DerivedCategory.Q.map (Pi.π I j))))
