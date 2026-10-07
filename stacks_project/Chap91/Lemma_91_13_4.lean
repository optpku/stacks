module

public import stacks_project.Chap91.Lemma_91_13_4_Trivial
public import stacks_project.Chap91.Lemma_91_13_3
import Mathlib.Tactic.CrossRefAttribute

/-!
# Classification of square-zero f⁻¹O_B-algebra extensions of O by G

Isomorphism classes of extensions 0 ⟶ G ⟶ O' ⟶ O ⟶ 0 of f⁻¹O_B-algebras in
which G is an ideal of square zero are canonically bijective to
Ext¹_O(NL_{O/O_B}, G), by specializing the torsor chart of Lemma 91.13.3 to
the identity diagram and the split solution G ⊕ O.
-/

@[expose] public section

open CategoryTheory
open SheafOfModules.RingedSite
open SheafOfModules.RingedSite.FirstOrderThickening
open SheafOfModules.RingedSite.FirstOrderThickening.Solution
open SheafOfModules.RingedSite.NaiveCotangent
open scoped DerivedExt SheafOfModules.RingedSite

noncomputable section

universe u

namespace SheafOfModules.RingedSite.FirstOrderThickening
namespace Solution

-- Local instance justification (defeq pin): `moduleCat_hasDerivedCategory` is reducible to `HasDerivedCategory.standard` and is not global; `ModuleDerived`, `singleFunctor`, and Ext must share that same derived-category instance.
attribute [local instance] RingedSite.Hom.moduleCat_hasDerivedCategory
-- Local instance justification (defeq pin): the commutative-sheaf presentation uses the same standard derived-category owner, exposed through the site-level spelling.
attribute [local instance] SheafOfModules.RingedSite.moduleCategoryHasDerivedCategory

variable {C : Type u} [Category.{u} C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
variable [J.HasSheafCompose (forget₂ RingCat.{u} AddCommGrpCat.{u})]
variable [HasWeakSheafify J CommRingCat.{u}]
variable [J.WEqualsLocallyBijective CommRingCat.{u}]
variable [HasWeakSheafify J AddCommGrpCat.{u}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
variable {O_B O : Sheaf J CommRingCat.{u}}
variable (fSharp : O_B ⟶ O)
variable (G : SheafOfModules (ringSheaf J O))

/-- Lemma 91.13.4 Let f : (Sh(C), O) ⟶ (Sh(B), O_B) be a morphism of
ringed topoi. Let G be an O-module. The set of isomorphism classes of
extensions of f⁻¹O_B-algebras 0 ⟶ G ⟶ O' ⟶ O ⟶ 0 where G is an ideal of
square zero is canonically bijective to Ext¹_O(NL_{O/O_B}, G). After
identifying underlying topoi, the Ext¹ group is
Ext⁽1⁾(Q NL(fSharp), Q(G[0])), and the classes are
`IsoClass (𝟙 O_B) (isSquareZero_id O_B) fSharp G (zeroKernelMap fSharp G)`,
based at the split solution `trivialSolution fSharp G`. -/
@[stacks 0GQ5]
def extensionEquiv :
    Ext⁽(1 : ℤ)⁾((moduleQ O).obj (NaiveCotangent.obj O_B (Under.mk fSharp)),
      (moduleQ O).obj ((CochainComplex.singleFunctor _ 0).obj G)) ≃
      IsoClass (𝟙 O_B) (isSquareZero_id O_B) fSharp G (zeroKernelMap fSharp G) :=
  isoClassEquiv (trivialSolution fSharp G)

/-- The based chart sends an Ext¹ class ξ to the translate of the split extension. -/
theorem extensionEquiv_apply
    (ξ : Ext⁽(1 : ℤ)⁾((moduleQ O).obj (NaiveCotangent.obj O_B (Under.mk fSharp)),
      (moduleQ O).obj ((CochainComplex.singleFunctor _ 0).obj G))) :
    extensionEquiv fSharp G ξ =
      ξ +ᵥ isoClassMk (trivialSolution fSharp G) := sorry

/-- The zero Ext¹ class is sent to the class of the split extension G ⊕ O. -/
theorem extensionEquiv_zero :
    extensionEquiv fSharp G 0 = isoClassMk (trivialSolution fSharp G) := sorry

/-- The inverse chart is torsor subtraction against the split extension. -/
theorem extensionEquiv_symm_apply
    (p : IsoClass (𝟙 O_B) (isSquareZero_id O_B) fSharp G (zeroKernelMap fSharp G)) :
    (extensionEquiv fSharp G).symm p =
      p -ᵥ isoClassMk (trivialSolution fSharp G) := sorry

/-- The source bijection is the torsor chart of Lemma 91.13.3 at the split solution. -/
theorem extensionEquiv_eq_isoClassEquiv :
    extensionEquiv fSharp G = isoClassEquiv (trivialSolution fSharp G) := sorry

end Solution
end SheafOfModules.RingedSite.FirstOrderThickening
