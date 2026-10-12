/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.Group.Action.Pretransitive
public import ReasLib.AlgebraicGeometry.Scheme.Module.Monoidal
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Deformation.Perturbation.Construction
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Deformation.Presheaf
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Thickening.Restriction

/-!
# The additive action on infinitesimal deformations

Sections of the pushed-forward internal-Hom sheaf act on compatible local deformations by
explicit perturbation. The action is natural under restriction and simply transitive whenever
a local deformation is chosen.
-/

@[expose] public section

open CategoryTheory Opposite TopologicalSpace
open SheafOfModules.RingedSite
open scoped AlgebraicGeometry RelativeDerivation

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Hom.Deformation

variable {S X X' Y Y' : Scheme.{u}}

/-- The additive sheaf of infinitesimal parameters for deformations of `a`, viewed on `X'`
through direct image along the first-order thickening `i`. -/
noncomputable def parameterSheaf (S : Scheme.{u}) (i : X ⟶ X') (a : X ⟶ Y)
    [X.Over S] [Y.Over S] [a.IsOver S] :
    TopCat.Sheaf AddCommGrpCat.{u} X'.toTopCat :=
  (TopCat.Sheaf.pushforward AddCommGrpCat.{u} i.base).obj
    ((SheafOfModules.toSheaf X.ringCatSheaf).obj
      (Scheme.Modules.internalHom
        ((Scheme.Modules.pullback a).obj Ω[(Y ↘ S).toShHom])
        (Scheme.Hom.conormalSheaf i)))

/-- On `U'`, the parameter sheaf is the local internal-Hom over `i ⁻¹ᵁ U'`. -/
theorem parameterSheaf_obj (S : Scheme.{u}) (i : X ⟶ X') (a : X ⟶ Y)
    [X.Over S] [Y.Over S] [a.IsOver S] (U' : X'.Opens) :
    (parameterSheaf S i a).1.obj (op U') =
      ((SheafOfModules.toSheaf X.ringCatSheaf).obj
        (Scheme.Modules.internalHom
          ((Scheme.Modules.pullback a).obj Ω[(Y ↘ S).toShHom])
          (Scheme.Hom.conormalSheaf i))).1.obj (op (i ⁻¹ᵁ U')) := sorry

/-- A section of the pushed-forward internal-Hom sheaf, interpreted as a morphism from the
pulled-back differentials to the conormal sheaf of the restricted thickening. -/
noncomputable def localParameterHom (S : Scheme.{u}) (i : X ⟶ X')
    (a : X ⟶ Y) [X.Over S] [Y.Over S] [IsFirstOrderThickening i]
    [a.IsOver S] (U' : X'.Opens) (θ : (parameterSheaf S i a).1.obj (op U')) :
    (Scheme.Modules.pullback ((i ⁻¹ᵁ U').ι ≫ a)).obj Ω[(Y ↘ S).toShHom] ⟶
      Scheme.Hom.conormalSheaf (i ∣_ U') :=
  (Scheme.Modules.pullbackComp (i ⁻¹ᵁ U').ι a).inv.app _ ≫
    (Scheme.Modules.restrictFunctorIsoPullback (i ⁻¹ᵁ U').ι).inv.app _ ≫
      (Scheme.Modules.overFunctorEquiv (i ⁻¹ᵁ U')).inv.app _ ≫
        (Scheme.Modules.overEquiv (i ⁻¹ᵁ U')).functor.map θ ≫
          (Scheme.Modules.overFunctorEquiv (i ⁻¹ᵁ U')).hom.app _ ≫
            (Scheme.Modules.restrictFunctorIsoPullback (i ⁻¹ᵁ U').ι).hom.app _ ≫
              Scheme.Hom.Conormal.map
                ((isPullback_morphismRestrict i U').flip.toCommSq)

/-- The underlying morphism of a compatible deformation section is canonically over `S`. -/
theorem section_isOver (S : Scheme.{u}) (i : X ⟶ X') (j : Y ⟶ Y')
    (a : X ⟶ Y) [X.Over S] [X'.Over S] [Y.Over S] [Y'.Over S]
    [IsFirstOrderThickening i] [IsFirstOrderThickening j]
    [i.IsOver S] [j.IsOver S] [a.IsOver S]
    (A : (Scheme.Modules.pullback a).obj (Scheme.Hom.conormalSheaf j) ⟶
      Scheme.Hom.conormalSheaf i) (U' : X'.Opens)
    (s : sections S i j a A U') : s.1.IsOver S := sorry

/-- A candidate morphism is the perturbation of a compatible deformation section prescribed
by a local differential parameter. -/
def IsSectionPerturbation (S : Scheme.{u}) (i : X ⟶ X') (j : Y ⟶ Y')
    (a : X ⟶ Y) [X.Over S] [X'.Over S] [Y.Over S] [Y'.Over S]
    [IsFirstOrderThickening i] [IsFirstOrderThickening j]
    [i.IsOver S] [j.IsOver S] [a.IsOver S]
    (A : (Scheme.Modules.pullback a).obj (Scheme.Hom.conormalSheaf j) ⟶
      Scheme.Hom.conormalSheaf i) (U' : X'.Opens)
    (s : sections S i j a A U')
    (θ : (Scheme.Modules.pullback ((i ⁻¹ᵁ U').ι ≫ a)).obj Ω[(Y ↘ S).toShHom] ⟶
      Scheme.Hom.conormalSheaf (i ∣_ U'))
    (b' : U'.toScheme ⟶ Y') : Prop :=
  @IsPerturbation _ _ _ _ S (i ∣_ U') j ((i ⁻¹ᵁ U').ι ≫ a) s.1
    _ _ _ _ _ _ _ _ _ (section_isOver S i j a A U' s)
    (Classical.choose s.2.2) θ b'

/-- The underlying morphism obtained by acting on a compatible local deformation with an
infinitesimal parameter. -/
noncomputable def actHom (S : Scheme.{u}) (i : X ⟶ X') (j : Y ⟶ Y')
    (a : X ⟶ Y) [X.Over S] [X'.Over S] [Y.Over S] [Y'.Over S]
    [IsFirstOrderThickening i] [IsFirstOrderThickening j]
    [i.IsOver S] [j.IsOver S] [a.IsOver S]
    (A : (Scheme.Modules.pullback a).obj (Scheme.Hom.conormalSheaf j) ⟶
      Scheme.Hom.conormalSheaf i) (U' : X'.Opens)
    (θ : (parameterSheaf S i a).1.obj (op U'))
    (s : sections S i j a A U') : U'.toScheme ⟶ Y' :=
  perturbHom S (i ∣_ U') j ((i ⁻¹ᵁ U').ι ≫ a) s.1
    (Classical.choose s.2.2) (localParameterHom S i a U' θ)

/-- Explicit perturbation preserves the compatibility conditions defining a local deformation. -/
theorem actHom_mem_sections (S : Scheme.{u}) (i : X ⟶ X') (j : Y ⟶ Y')
    (a : X ⟶ Y) [X.Over S] [X'.Over S] [Y.Over S] [Y'.Over S]
    [IsFirstOrderThickening i] [IsFirstOrderThickening j]
    [i.IsOver S] [j.IsOver S] [a.IsOver S]
    (A : (Scheme.Modules.pullback a).obj (Scheme.Hom.conormalSheaf j) ⟶
      Scheme.Hom.conormalSheaf i) (U' : X'.Opens)
    (θ : (parameterSheaf S i a).1.obj (op U'))
    (s : sections S i j a A U') :
    actHom S i j a A U' θ s ∈ sections S i j a A U' := sorry

/-- The explicit action of an infinitesimal parameter on a compatible local deformation. -/
noncomputable def act (S : Scheme.{u}) (i : X ⟶ X') (j : Y ⟶ Y')
    (a : X ⟶ Y) [X.Over S] [X'.Over S] [Y.Over S] [Y'.Over S]
    [IsFirstOrderThickening i] [IsFirstOrderThickening j]
    [i.IsOver S] [j.IsOver S] [a.IsOver S]
    (A : (Scheme.Modules.pullback a).obj (Scheme.Hom.conormalSheaf j) ⟶
      Scheme.Hom.conormalSheaf i) (U' : X'.Opens)
    (θ : (parameterSheaf S i a).1.obj (op U'))
    (s : sections S i j a A U') : sections S i j a A U' :=
  ⟨actHom S i j a A U' θ s, actHom_mem_sections S i j a A U' θ s⟩

/-- Acting by `θ` gives the perturbation prescribed by the corresponding local parameter
homomorphism. -/
theorem act_isPerturbation (S : Scheme.{u}) (i : X ⟶ X') (j : Y ⟶ Y')
    (a : X ⟶ Y) [X.Over S] [X'.Over S] [Y.Over S] [Y'.Over S]
    [IsFirstOrderThickening i] [IsFirstOrderThickening j]
    [i.IsOver S] [j.IsOver S] [a.IsOver S]
    (A : (Scheme.Modules.pullback a).obj (Scheme.Hom.conormalSheaf j) ⟶
      Scheme.Hom.conormalSheaf i) (U' : X'.Opens)
    (θ : (parameterSheaf S i a).1.obj (op U'))
    (s : sections S i j a A U') :
    IsSectionPerturbation S i j a A U' s (localParameterHom S i a U' θ)
      (act S i j a A U' θ s).1 := sorry

/-- Acting by the zero infinitesimal parameter fixes a deformation section. -/
theorem act_zero (S : Scheme.{u}) (i : X ⟶ X') (j : Y ⟶ Y')
    (a : X ⟶ Y) [X.Over S] [X'.Over S] [Y.Over S] [Y'.Over S]
    [IsFirstOrderThickening i] [IsFirstOrderThickening j]
    [i.IsOver S] [j.IsOver S] [a.IsOver S]
    (A : (Scheme.Modules.pullback a).obj (Scheme.Hom.conormalSheaf j) ⟶
      Scheme.Hom.conormalSheaf i) (U' : X'.Opens)
    (s : sections S i j a A U') : act S i j a A U' 0 s = s := sorry

/-- Acting by a sum is successive action by its two infinitesimal parameters. -/
theorem act_add (S : Scheme.{u}) (i : X ⟶ X') (j : Y ⟶ Y')
    (a : X ⟶ Y) [X.Over S] [X'.Over S] [Y.Over S] [Y'.Over S]
    [IsFirstOrderThickening i] [IsFirstOrderThickening j]
    [i.IsOver S] [j.IsOver S] [a.IsOver S]
    (A : (Scheme.Modules.pullback a).obj (Scheme.Hom.conormalSheaf j) ⟶
      Scheme.Hom.conormalSheaf i) (U' : X'.Opens)
    (θ η : (parameterSheaf S i a).1.obj (op U'))
    (s : sections S i j a A U') :
    act S i j a A U' (θ + η) s =
      act S i j a A U' θ (act S i j a A U' η s) := sorry

/-- The additive action of infinitesimal parameters on compatible local deformations. -/
@[implicit_reducible]
noncomputable def addAction (S : Scheme.{u}) (i : X ⟶ X') (j : Y ⟶ Y')
    (a : X ⟶ Y) [X.Over S] [X'.Over S] [Y.Over S] [Y'.Over S]
    [IsFirstOrderThickening i] [IsFirstOrderThickening j]
    [i.IsOver S] [j.IsOver S] [a.IsOver S]
    (A : (Scheme.Modules.pullback a).obj (Scheme.Hom.conormalSheaf j) ⟶
      Scheme.Hom.conormalSheaf i) (U' : X'.Opens) :
    AddAction ((parameterSheaf S i a).1.obj (op U'))
      ((sheaf S i j a A).1.obj (op U')) where
  vadd := act S i j a A U'
  zero_vadd := act_zero S i j a A U'
  add_vadd := act_add S i j a A U'

/-- The deformation action commutes with restriction to a smaller open. -/
theorem act_naturality (S : Scheme.{u}) (i : X ⟶ X') (j : Y ⟶ Y')
    (a : X ⟶ Y) [X.Over S] [X'.Over S] [Y.Over S] [Y'.Over S]
    [IsFirstOrderThickening i] [IsFirstOrderThickening j]
    [i.IsOver S] [j.IsOver S] [a.IsOver S]
    (A : (Scheme.Modules.pullback a).obj (Scheme.Hom.conormalSheaf j) ⟶
      Scheme.Hom.conormalSheaf i) {U' V' : X'.Opens} (h : V' ≤ U')
    (θ : (parameterSheaf S i a).1.obj (op U'))
    (s : sections S i j a A U') :
    restrictSection S i j a A h (act S i j a A U' θ s) =
      act S i j a A V'
        ((parameterSheaf S i a).1.map (homOfLE h).op θ)
        (restrictSection S i j a A h s) := sorry

/-- The explicit additive deformation action is pretransitive on every open. -/
theorem act_isPretransitive (S : Scheme.{u}) (i : X ⟶ X') (j : Y ⟶ Y')
    (a : X ⟶ Y) [X.Over S] [X'.Over S] [Y.Over S] [Y'.Over S]
    [IsFirstOrderThickening i] [IsFirstOrderThickening j]
    [i.IsOver S] [j.IsOver S] [a.IsOver S]
    (A : (Scheme.Modules.pullback a).obj (Scheme.Hom.conormalSheaf j) ⟶
      Scheme.Hom.conormalSheaf i) (U' : X'.Opens) :
    @AddAction.IsPretransitive ((parameterSheaf S i a).1.obj (op U'))
      ((sheaf S i j a A).1.obj (op U')) (addAction S i j a A U').toVAdd := sorry

/-- The explicit additive deformation action is free on every open. -/
theorem act_isCancelVAdd (S : Scheme.{u}) (i : X ⟶ X') (j : Y ⟶ Y')
    (a : X ⟶ Y) [X.Over S] [X'.Over S] [Y.Over S] [Y'.Over S]
    [IsFirstOrderThickening i] [IsFirstOrderThickening j]
    [i.IsOver S] [j.IsOver S] [a.IsOver S]
    (A : (Scheme.Modules.pullback a).obj (Scheme.Hom.conormalSheaf j) ⟶
      Scheme.Hom.conormalSheaf i) (U' : X'.Opens) :
    @IsCancelVAdd ((parameterSheaf S i a).1.obj (op U'))
      ((sheaf S i j a A).1.obj (op U')) (addAction S i j a A U').toVAdd := sorry

/-- Translation by a chosen compatible deformation section is bijective. -/
theorem act_simplyTransitive (S : Scheme.{u}) (i : X ⟶ X') (j : Y ⟶ Y')
    (a : X ⟶ Y) [X.Over S] [X'.Over S] [Y.Over S] [Y'.Over S]
    [IsFirstOrderThickening i] [IsFirstOrderThickening j]
    [i.IsOver S] [j.IsOver S] [a.IsOver S]
    (A : (Scheme.Modules.pullback a).obj (Scheme.Hom.conormalSheaf j) ⟶
      Scheme.Hom.conormalSheaf i) (U' : X'.Opens)
    (s : sections S i j a A U') :
    Function.Bijective
      (fun θ : (parameterSheaf S i a).1.obj (op U') ↦ act S i j a A U' θ s) := sorry

end AlgebraicGeometry.Scheme.Hom.Deformation
