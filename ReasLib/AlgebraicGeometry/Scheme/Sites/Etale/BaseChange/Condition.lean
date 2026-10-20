module

public import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
public import Mathlib.AlgebraicGeometry.Pullbacks
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.Pullback
public import ReasLib.CategoryTheory.Sites.HigherDirectImage
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.BaseChange.Map

@[expose] public section

open CategoryTheory
open AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Etale

/-- The étale base-change condition for `f : X ⟶ S` and `n : ℤ` through degree `q₀`
requires the supplied maps `(f')⁻¹ R^q g_* F ⟶ R^q h_* e⁻¹ F` to be isomorphisms
for every base change `f'` of `f`, every cartesian square with `g` quasi-compact
and quasi-separated, every abelian sheaf `F` annihilated by `n`, and every
`q ≤ q₀`. The inverse-image functors and base-change maps are explicit inputs. -/
def baseChangeCondition
    {X S : Scheme.{u}} (f : X ⟶ S) (n : ℤ) (q₀ : ℕ)
    (invImg : ∀ {A B : Scheme.{u}}, (A ⟶ B) →
      Sheaf B.smallEtaleTopology AddCommGrpCat.{u} ⥤
        Sheaf A.smallEtaleTopology AddCommGrpCat.{u})
    (baseChangeMap :
      ∀ {X' Y S' T : Scheme.{u}}
        (p : X' ⟶ X) (f' : X' ⟶ S') (s : S' ⟶ S)
        (h : Y ⟶ X') (e : Y ⟶ T) (g : T ⟶ S')
        [QuasiCompact g] [QuasiSeparated g]
        [HasSheafify T.smallEtaleTopology AddCommGrpCat.{u}]
        [HasSheafify S'.smallEtaleTopology AddCommGrpCat.{u}]
        [HasSheafify X'.smallEtaleTopology AddCommGrpCat.{u}]
        [HasSheafify Y.smallEtaleTopology AddCommGrpCat.{u}]
        [HasInjectiveResolutions
          (Sheaf T.smallEtaleTopology AddCommGrpCat.{u})]
        [HasInjectiveResolutions
          (Sheaf Y.smallEtaleTopology AddCommGrpCat.{u})],
        IsPullback p f' f s → IsPullback h e f' g →
        (F : Sheaf T.smallEtaleTopology AddCommGrpCat.{u}) → (q : ℕ) →
        (invImg f').obj
            (Sheaf.higherDirectImage (Scheme.smallEtalePullback g) F q) ⟶
          Sheaf.higherDirectImage (Scheme.smallEtalePullback h)
            ((invImg e).obj F) q)
    : Prop :=
  ∀ {X' Y S' T : Scheme.{u}}
    (p : X' ⟶ X) (f' : X' ⟶ S') (s : S' ⟶ S)
    (h : Y ⟶ X') (e : Y ⟶ T) (g : T ⟶ S')
    [QuasiCompact g] [QuasiSeparated g]
    [HasSheafify T.smallEtaleTopology AddCommGrpCat.{u}]
    [HasSheafify S'.smallEtaleTopology AddCommGrpCat.{u}]
    [HasSheafify X'.smallEtaleTopology AddCommGrpCat.{u}]
    [HasSheafify Y.smallEtaleTopology AddCommGrpCat.{u}]
    [HasInjectiveResolutions
      (Sheaf T.smallEtaleTopology AddCommGrpCat.{u})]
    [HasInjectiveResolutions
      (Sheaf Y.smallEtaleTopology AddCommGrpCat.{u})]
    (sq₁ : IsPullback p f' f s) (sq₂ : IsPullback h e f' g),
    (F : Sheaf T.smallEtaleTopology AddCommGrpCat.{u}) →
    (h_annihilated : (n : ℤ) • 𝟙 F = 0) →
    ∀ q : ℕ, q ≤ q₀ →
      IsIso (baseChangeMap p f' s h e g sq₁ sq₂ F q)

/-- The étale base-change condition through degree `q₁` implies the condition
through every smaller degree bound `q₀ ≤ q₁`, with the same inverse-image
functors and base-change maps. -/
theorem baseChangeCondition_mono
    {X S : Scheme.{u}} (f : X ⟶ S) (n : ℤ) {q₀ q₁ : ℕ}
    (hbound : q₀ ≤ q₁)
    (invImg : ∀ {A B : Scheme.{u}}, (A ⟶ B) →
      Sheaf B.smallEtaleTopology AddCommGrpCat.{u} ⥤
        Sheaf A.smallEtaleTopology AddCommGrpCat.{u})
    (baseChangeMap :
      ∀ {X' Y S' T : Scheme.{u}}
        (p : X' ⟶ X) (f' : X' ⟶ S') (s : S' ⟶ S)
        (h : Y ⟶ X') (e : Y ⟶ T) (g : T ⟶ S')
        [QuasiCompact g] [QuasiSeparated g]
        [HasSheafify T.smallEtaleTopology AddCommGrpCat.{u}]
        [HasSheafify S'.smallEtaleTopology AddCommGrpCat.{u}]
        [HasSheafify X'.smallEtaleTopology AddCommGrpCat.{u}]
        [HasSheafify Y.smallEtaleTopology AddCommGrpCat.{u}]
        [HasInjectiveResolutions
          (Sheaf T.smallEtaleTopology AddCommGrpCat.{u})]
        [HasInjectiveResolutions
          (Sheaf Y.smallEtaleTopology AddCommGrpCat.{u})],
        IsPullback p f' f s → IsPullback h e f' g →
        (F : Sheaf T.smallEtaleTopology AddCommGrpCat.{u}) → (q : ℕ) →
        (invImg f').obj
            (Sheaf.higherDirectImage (Scheme.smallEtalePullback g) F q) ⟶
          Sheaf.higherDirectImage (Scheme.smallEtalePullback h)
            ((invImg e).obj F) q) :
    baseChangeCondition f n q₁ invImg baseChangeMap →
      baseChangeCondition f n q₀ invImg baseChangeMap := sorry

namespace BaseChange

/-- The canonical étale base-change condition through a specified degree bound. -/
def Holds {X S : Scheme.{u}} (f : X ⟶ S) (n : ℤ) (bound : ℕ) : Prop :=
  ∀ {X' Y S' T : Scheme.{u}}
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
    (sq₁ : IsPullback p f' f s) (sq₂ : IsPullback h e f' g),
    ∀ (F : Sheaf T.smallEtaleTopology AddCommGrpCat.{u + 1}),
      (n : ℤ) • 𝟙 F = 0 →
      ∀ q : ℕ, q ≤ bound → IsIso (higherMap f' h e g sq₂ q F)

end BaseChange

end AlgebraicGeometry.Scheme.Etale

end

end
