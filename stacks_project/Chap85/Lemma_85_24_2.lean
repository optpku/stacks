module

public import Mathlib.Tactic.CrossRefAttribute
public import stacks_project.Chap85.Lemma_85_24_2_Cartesian
public import stacks_project.Chap85.Lemma_85_24_2_Component
public import stacks_project.Chap85.Lemma_85_24_2_System

/-!
# Lemma 85.24.2

In Situation 85.24.1, vanishing of negative self-Exts of each `E_U` produces a cartesian
object of `D(O)` on `((C / u(L))_total, O)` whose restriction to each
`D(O_{C / u(U_{n,i})})` recovers `E_{U_{n,i}}` compatibly, uniquely up to unique
isomorphism.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite
open RingedSite
open RingedSite.Hom
open RingedSite.ModuleDerived
open RingedSite.Localization.AtSimplicialSR
open RingedSite.Localization.AtSimplicialSR.ModuleDerived
open scoped SemiRepresentableFamily Simplicial

noncomputable section

universe ι u v w uB vB

open SemiRepresentableFamily
  (OverSite overTopology overSiteDiagram overSiteTotalTopology totalForget overMap)

namespace RingedSite.ModuleDerived.LocallyGiven

variable {X : RingedSite.{u, v, w}}
variable {h_univLE_carrier : UnivLE.{max u v, w}}
variable {B : Type uB} [Category.{vB} B]
variable (D : @LocallyGiven.{u, v, w, w, uB, vB} h_univLE_carrier X B inferInstance)
variable (L : SimplicialObject (FormalCoproduct.{ι} B))
variable [h_univLE_index : UnivLE.{max ι u v, w}]
variable [HasSheafify (overSiteTotalTopology X.siteTopology (simplicialK h_univLE_carrier D L)) (Type w)]
variable [HasWeakSheafify (overSiteTotalTopology X.siteTopology (simplicialK h_univLE_carrier D L)) (Type w)]
variable [∀ n : SimplexCategory,
    HasSheafify (overTopology X.siteTopology ((simplicialK h_univLE_carrier D L).obj (op n))) (Type w)]
variable [∀ n : SimplexCategory,
    HasWeakSheafify (overTopology X.siteTopology ((simplicialK h_univLE_carrier D L).obj (op n))) (Type w)]
variable [∀ P : (Grothendieck (overSiteDiagram (simplicialK h_univLE_carrier D L)))ᵒᵖ ⥤ Type w,
    (totalForget (simplicialK h_univLE_carrier D L)).op.HasPointwiseRightKanExtension P]
variable [∀ n : SimplexCategory,
    ∀ P : (OverSite ((simplicialK h_univLE_carrier D L).obj (op n)))ᵒᵖ ⥤ Type w,
      (Grothendieck.ι (overSiteDiagram (simplicialK h_univLE_carrier D L)) (op n)).op.HasPointwiseRightKanExtension P]
variable [∀ {m n : SimplexCategory} (φ : m ⟶ n),
    ∀ P : (OverSite ((simplicialK h_univLE_carrier D L).obj (op n)))ᵒᵖ ⥤ Type w,
      (overMap ((simplicialK h_univLE_carrier D L).map φ.op)).op.HasPointwiseRightKanExtension P]
variable [(overSiteTotalTopology X.siteTopology (simplicialK h_univLE_carrier D L)).HasSheafCompose
    (CategoryTheory.forget RingCat.{w})]
variable [X.siteTopology.HasSheafCompose (CategoryTheory.forget RingCat.{w})]
variable [∀ n : SimplexCategory,
    (overTopology X.siteTopology ((simplicialK h_univLE_carrier D L).obj (op n))).HasSheafCompose
      (CategoryTheory.forget RingCat.{w})]
variable [(SheafOfModules.restrictScalars.{w}
    (toAmbient (simplicialK h_univLE_carrier D L)).structureMap).IsRightAdjoint]
variable [∀ n : SimplexCategory,
    (SheafOfModules.restrictScalars.{w}
      (stageIncl (simplicialK h_univLE_carrier D L) n).structureMap).IsRightAdjoint]
variable [∀ {m n : SimplexCategory} (φ : m ⟶ n),
    (SheafOfModules.restrictScalars.{w}
      (stageMap (simplicialK h_univLE_carrier D L) φ).structureMap).IsRightAdjoint]

/-- Lemma 85.24.2 (1)
In Situation 85.24.1, assume negative self-Exts of `E_U` in `D(O_{u(U)})` vanish. Let
`L` be a simplicial object of `SR(B)`, write `K = u(L)`, and let `((C / K)_total, O)`
be as in Remark 85.16.5. There exists a cartesian object `E` of `D(O)` whose restriction
to each `D(O_{C / u(U_{n,i})})` is `E_{U_{n,i}}` compatibly. -/
@[stacks 0DCA]
theorem exists_isCartesian_compatibleRestriction (h_neg : negativeSelfExt h_univLE_carrier D) :
    ∃ (E : Hom.ModuleDerived.{w} (site (simplicialK h_univLE_carrier D L)))
      (hE : CompatibleRestriction D L E),
      IsCartesian (simplicialK h_univLE_carrier D L) E :=
  sorry

/-- Lemma 85.24.2 (2)
In the situation of Lemma 85.24.2 (1), a cartesian compatible restriction is unique
up to unique isomorphism. -/
@[stacks 0DCA]
theorem unique_hom_isCartesian_compatibleRestriction (h_neg : negativeSelfExt h_univLE_carrier D)
    (E E' : Hom.ModuleDerived.{w} (site (simplicialK h_univLE_carrier D L)))
    [IsCartesian (simplicialK h_univLE_carrier D L) E]
    [IsCartesian (simplicialK h_univLE_carrier D L) E']
    (hE : CompatibleRestriction D L E) (hE' : CompatibleRestriction D L E') :
    ∃ (e : E ≅ E'),
      CompatibleRestriction.IsCompatibleIso D L hE hE' e ∧
        ∀ e' : E ≅ E',
          CompatibleRestriction.IsCompatibleIso D L hE hE' e' → e'.hom = e.hom :=
  sorry

end RingedSite.ModuleDerived.LocallyGiven
