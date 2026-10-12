/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.BaseChange.Condition
public import Mathlib.Algebra.Category.ModuleCat.Basic
public import Mathlib.CategoryTheory.Preadditive.Injective.Basic
public import Mathlib.CategoryTheory.Sites.Whiskering

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Etale.BaseChange

variable {X S X' Y S' T : Scheme.{u}}

/-- Under the canonical base-change condition through degree `q - 1`, the degree-`q`
base-change comparison is a monomorphism. -/
theorem higherMap_mono
    (f : X ⟶ S) (n : ℤ) {q : ℕ} (hq : 1 ≤ q)
    (p : X' ⟶ X) (f' : X' ⟶ S') (s : S' ⟶ S)
    (h : Y ⟶ X') (e : Y ⟶ T) (g : T ⟶ S')
    [QuasiCompact g] [QuasiSeparated g]
    [HasSheafify T.smallEtaleTopology AddCommGrpCat.{u + 1}]
    [HasSheafify S'.smallEtaleTopology AddCommGrpCat.{u + 1}]
    [HasSheafify X'.smallEtaleTopology AddCommGrpCat.{u + 1}]
    [HasSheafify Y.smallEtaleTopology AddCommGrpCat.{u + 1}]
    [HasInjectiveResolutions
      (Sheaf T.smallEtaleTopology AddCommGrpCat.{u + 1})]
    [HasInjectiveResolutions
      (Sheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1})]
    (sq₁ : IsPullback p f' f s) (sq₂ : IsPullback h e f' g)
    (hBC : Holds f n (q - 1))
    (F : Sheaf T.smallEtaleTopology AddCommGrpCat.{u + 1})
    (hF : (n : ℤ) • 𝟙 F = 0) :
    Mono (higherMap f' h e g sq₂ q F) := sorry

/-- The degree-`q` base-change comparison followed by the map induced by a
coefficient inclusion into an injective module sheaf is zero. -/
theorem higherMap_comp_eq_zero_of_injective
    (n : ℤ) (f' : X' ⟶ S') (h : Y ⟶ X') (e : Y ⟶ T) (g : T ⟶ S')
    [QuasiCompact g] [QuasiSeparated g]
    [HasSheafify T.smallEtaleTopology AddCommGrpCat.{u + 1}]
    [HasSheafify S'.smallEtaleTopology AddCommGrpCat.{u + 1}]
    [HasSheafify X'.smallEtaleTopology AddCommGrpCat.{u + 1}]
    [HasSheafify Y.smallEtaleTopology AddCommGrpCat.{u + 1}]
    [HasInjectiveResolutions
      (Sheaf T.smallEtaleTopology AddCommGrpCat.{u + 1})]
    [HasInjectiveResolutions
      (Sheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1})]
    (sq₂ : IsPullback h e f' g) {q : ℕ} (hq : 1 ≤ q)
    (F : Sheaf T.smallEtaleTopology AddCommGrpCat.{u + 1})
    (Gmod : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} (ZMod n.natAbs)))
    [Injective Gmod]
    (ι : F ⟶ (sheafCompose T.smallEtaleTopology
      (forget₂ (ModuleCat.{u + 1} (ZMod n.natAbs)) AddCommGrpCat.{u + 1})).obj Gmod) :
    higherMap f' h e g sq₂ q F ≫
        (Derived.higherDirectImage h q).map
          ((Abelian.inverseImage e).map ι) = 0 := sorry

/-- The canonical morphism from the cokernel of a base-change comparison to the
higher direct image of the underlying injective coefficient sheaf. -/
noncomputable def higherCokernelToInjective
    (n : ℤ) (f' : X' ⟶ S') (h : Y ⟶ X') (e : Y ⟶ T) (g : T ⟶ S')
    [QuasiCompact g] [QuasiSeparated g]
    [HasSheafify T.smallEtaleTopology AddCommGrpCat.{u + 1}]
    [HasSheafify S'.smallEtaleTopology AddCommGrpCat.{u + 1}]
    [HasSheafify X'.smallEtaleTopology AddCommGrpCat.{u + 1}]
    [HasSheafify Y.smallEtaleTopology AddCommGrpCat.{u + 1}]
    [HasInjectiveResolutions
      (Sheaf T.smallEtaleTopology AddCommGrpCat.{u + 1})]
    [HasInjectiveResolutions
      (Sheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1})]
    (sq₂ : IsPullback h e f' g) {q : ℕ} (hq : 1 ≤ q)
    (F : Sheaf T.smallEtaleTopology AddCommGrpCat.{u + 1})
    (Gmod : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} (ZMod n.natAbs)))
    [Injective Gmod]
    (ι : F ⟶ (sheafCompose T.smallEtaleTopology
      (forget₂ (ModuleCat.{u + 1} (ZMod n.natAbs)) AddCommGrpCat.{u + 1})).obj Gmod) :
    cokernel (higherMap f' h e g sq₂ q F) ⟶
      (Derived.higherDirectImage h q).obj
        ((Abelian.inverseImage e).obj
          ((sheafCompose T.smallEtaleTopology
            (forget₂ (ModuleCat.{u + 1} (ZMod n.natAbs)) AddCommGrpCat.{u + 1})).obj Gmod)) :=
  cokernel.desc (higherMap f' h e g sq₂ q F)
    ((Derived.higherDirectImage h q).map ((Abelian.inverseImage e).map ι))
    (higherMap_comp_eq_zero_of_injective n f' h e g sq₂ hq F Gmod ι)

/-- The projection of the canonical cokernel morphism factors through the
coefficient map into the higher direct image. -/
theorem higherCokernelToInjective_spec
    (n : ℤ) (f' : X' ⟶ S') (h : Y ⟶ X') (e : Y ⟶ T) (g : T ⟶ S')
    [QuasiCompact g] [QuasiSeparated g]
    [HasSheafify T.smallEtaleTopology AddCommGrpCat.{u + 1}]
    [HasSheafify S'.smallEtaleTopology AddCommGrpCat.{u + 1}]
    [HasSheafify X'.smallEtaleTopology AddCommGrpCat.{u + 1}]
    [HasSheafify Y.smallEtaleTopology AddCommGrpCat.{u + 1}]
    [HasInjectiveResolutions
      (Sheaf T.smallEtaleTopology AddCommGrpCat.{u + 1})]
    [HasInjectiveResolutions
      (Sheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1})]
    (sq₂ : IsPullback h e f' g) {q : ℕ} (hq : 1 ≤ q)
    (F : Sheaf T.smallEtaleTopology AddCommGrpCat.{u + 1})
    (Gmod : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} (ZMod n.natAbs)))
    [Injective Gmod]
    (ι : F ⟶ (sheafCompose T.smallEtaleTopology
      (forget₂ (ModuleCat.{u + 1} (ZMod n.natAbs)) AddCommGrpCat.{u + 1})).obj Gmod) :
    cokernel.π (higherMap f' h e g sq₂ q F) ≫
        higherCokernelToInjective n f' h e g sq₂ hq F Gmod ι =
      (Derived.higherDirectImage h q).map ((Abelian.inverseImage e).map ι) := sorry

/-- Under the base-change condition, the canonical cokernel morphism into an
injective coefficient sheaf is a monomorphism. -/
theorem higherCokernelToInjective_mono
    (n : ℤ) (f : X ⟶ S) {q : ℕ} (hq : 1 ≤ q)
    (p : X' ⟶ X) (f' : X' ⟶ S') (s : S' ⟶ S)
    (h : Y ⟶ X') (e : Y ⟶ T) (g : T ⟶ S')
    [QuasiCompact g] [QuasiSeparated g]
    [HasSheafify T.smallEtaleTopology AddCommGrpCat.{u + 1}]
    [HasSheafify S'.smallEtaleTopology AddCommGrpCat.{u + 1}]
    [HasSheafify X'.smallEtaleTopology AddCommGrpCat.{u + 1}]
    [HasSheafify Y.smallEtaleTopology AddCommGrpCat.{u + 1}]
    [HasInjectiveResolutions
      (Sheaf T.smallEtaleTopology AddCommGrpCat.{u + 1})]
    [HasInjectiveResolutions
      (Sheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1})]
    (sq₁ : IsPullback p f' f s) (sq₂ : IsPullback h e f' g)
    (hBC : Holds f n (q - 1))
    (F : Sheaf T.smallEtaleTopology AddCommGrpCat.{u + 1})
    (hF : (n : ℤ) • 𝟙 F = 0)
    (Gmod : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} (ZMod n.natAbs)))
    [Injective Gmod]
    (ι : F ⟶ (sheafCompose T.smallEtaleTopology
      (forget₂ (ModuleCat.{u + 1} (ZMod n.natAbs)) AddCommGrpCat.{u + 1})).obj Gmod)
    [Mono ι] :
    Mono (higherCokernelToInjective n f' h e g sq₂ hq F Gmod ι) := sorry

/-- A monomorphism between `n`-annihilated coefficient sheaves induces a
monomorphism between the cokernels of their degree-`q` base-change maps. -/
theorem higherCokernelMap_mono
    (n : ℤ) (f : X ⟶ S) {q : ℕ} (hq : 1 ≤ q)
    (p : X' ⟶ X) (f' : X' ⟶ S') (s : S' ⟶ S)
    (h : Y ⟶ X') (e : Y ⟶ T) (g : T ⟶ S')
    [QuasiCompact g] [QuasiSeparated g]
    [HasSheafify T.smallEtaleTopology AddCommGrpCat.{u + 1}]
    [HasSheafify S'.smallEtaleTopology AddCommGrpCat.{u + 1}]
    [HasSheafify X'.smallEtaleTopology AddCommGrpCat.{u + 1}]
    [HasSheafify Y.smallEtaleTopology AddCommGrpCat.{u + 1}]
    [HasInjectiveResolutions
      (Sheaf T.smallEtaleTopology AddCommGrpCat.{u + 1})]
    [HasInjectiveResolutions
      (Sheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1})]
    (sq₁ : IsPullback p f' f s) (sq₂ : IsPullback h e f' g)
    (hBC : Holds f n (q - 1))
    {F G : Sheaf T.smallEtaleTopology AddCommGrpCat.{u + 1}}
    (ι : F ⟶ G) [Mono ι]
    (hF : (n : ℤ) • 𝟙 F = 0) (hG : (n : ℤ) • 𝟙 G = 0) :
    Mono (higherCokernelMap f' h e g sq₂ q ι) := sorry

end AlgebraicGeometry.Scheme.Etale.BaseChange

end
