module

public import stacks_project.Chap42.Lemma_42_54_7_VirtualNormal
public import stacks_project.Chap42.Lemma_42_54_2_BivariantClass
public import ReasLib.AlgebraicGeometry.BivariantClass.ZeroScheme

@[expose] public section

open AlgebraicGeometry CategoryTheory

noncomputable section

universe u

namespace AlgebraicGeometry
namespace Scheme
namespace Hom
namespace VirtualNormalBundle

/-- Lemma 42.54.7: for a scheme locally of finite type over a situation `(S, δ)`, the
degree-one Gysin bivariant class of a zero-scheme triple `(ℒ, s, i : D ⟶ X)` equals the
degree-one virtual-normal class `c(D ⟶ X, 𝒩)` formed from `𝒩 = i*ℒ`. -/
@[stacks 0FBN]
theorem gysin_eq_ofZeroScheme
    {S X : Scheme.{u}} [UniversallyCatenary S]
    (δ : S → ℤ) [IsDimensionFunction δ]
    (p : X ⟶ S) [LocallyOfFiniteType p]
    (ℒ : X.Modules) [Scheme.Modules.Invertible ℒ] (s : ℒ.sections)
    [LocallyOfFiniteType (zeroSchemeι ℒ s ≫ p)]
    (D : ClosedSpecialization δ (zeroSchemeι ℒ s ≫ p) p
      (zeroSchemeι ℒ s) rfl (ofZeroScheme ℒ s)) :
    @BivariantClass.gysin S _ δ _ (Over.mk p) _ ℒ
        ‹Scheme.Modules.Invertible ℒ› s =
      globalClassOfRank δ (zeroSchemeι ℒ s ≫ p) p (zeroSchemeι ℒ s) rfl
        (ofZeroScheme ℒ s) D 1 := sorry

end VirtualNormalBundle
end Hom
end Scheme
end AlgebraicGeometry
