module

public import ReasLib.AlgebraicGeometry.Scheme.DeRham.FormComparison
public import ReasLib.AlgebraicGeometry.Scheme.Differentials.TraceRule
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.ExteriorPower.Multiplication
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.ExteriorPower.DegreeZero

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits ComplexShape TopologicalSpace
open CategoryTheory.MonoidalCategory
open SheafOfModules.RingedSite
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.RelativeDifferentials

namespace TraceRule

/-- The absolute square regarded as a square of underlying ringed spaces. -/
abbrev absoluteRingedSquare {X Y : Scheme.{u}} (f : Y ⟶ X) :=
  (absoluteSquare f).map
    (Scheme.forgetToLocallyRingedSpace ⋙ LocallyRingedSpace.forgetToSheafedSpace)

/-- The coefficient map of the absolute square followed by the pushed-forward structure map is
the restriction of the usual structure-sheaf map along `Spec(ℤ)`. -/
theorem absoluteStructureMap {X Y : Scheme.{u}} (f : Y ⟶ X) :
    (RingedSpace.DeRham.baseChangeHom (absoluteRingedSquare f)).structureSheafMap ≫
        ((Opens.map f.base).sheafPushforwardContinuous
          RingCat (Opens.grothendieckTopology X)
            (Opens.grothendieckTopology Y)).map
            (TopCat.Sheaf.ringSheafOfCommMap
              (RingedSpace.DeRham.structureMap
                (terminal.from Y).toLRSHom.toShHom)) =
      TopCat.Sheaf.ringSheafOfCommMap
          (RingedSpace.DeRham.structureMap
            (terminal.from X).toLRSHom.toShHom) ≫
        RingedSpace.Hom.toRingCatSheafHom f.toLRSHom.toShHom := sorry

/-- The comparison identifying coefficient pushforward of an absolute form with scalar
restriction of its usual scheme-theoretic pushforward. -/
noncomputable def componentSourceIso {X Y : Scheme.{u}} (f : Y ⟶ X) (p : ℕ) :
    (RingedSpace.DeRham.pushforward (absoluteRingedSquare f)).obj
        (RingedSpace.DeRham.term (terminal.from Y).toLRSHom.toShHom p) ≅
      (DeRham.restriction
        (RingedSpace.DeRham.structureMap (terminal.from X).toLRSHom.toShHom)).obj
          ((Scheme.Modules.toRingedSpace X).obj
            ((Scheme.Modules.pushforward f).obj
              ((Scheme.Modules.fromRingedSpace Y).obj
                (RingedSpace.DeRham.form
                  (terminal.from Y).toLRSHom.toShHom p)))) :=
  (SheafOfModules.restrictPushforwardIso
      (F := Opens.map f.base) (J := Opens.grothendieckTopology X)
      (K := Opens.grothendieckTopology Y)
      (TopCat.Sheaf.ringSheafOfCommMap
        (RingedSpace.DeRham.structureMap (terminal.from Y).toLRSHom.toShHom))
      (RingedSpace.DeRham.baseChangeHom (absoluteRingedSquare f)).structureSheafMap
      (TopCat.Sheaf.ringSheafOfCommMap
          (RingedSpace.DeRham.structureMap (terminal.from X).toLRSHom.toShHom) ≫
        RingedSpace.Hom.toRingCatSheafHom f.toLRSHom.toShHom)
      (absoluteStructureMap f)).app
        (RingedSpace.DeRham.form (terminal.from Y).toLRSHom.toShHom p) ≪≫
    (SheafOfModules.pushforwardRestrictIso
      (F := Opens.map f.base) (J := Opens.grothendieckTopology X)
      (K := Opens.grothendieckTopology Y)
      (TopCat.Sheaf.ringSheafOfCommMap
        (RingedSpace.DeRham.structureMap (terminal.from X).toLRSHom.toShHom))
      (RingedSpace.Hom.toRingCatSheafHom f.toLRSHom.toShHom)).symm.app
        (RingedSpace.DeRham.form (terminal.from Y).toLRSHom.toShHom p)

/-- The absolute trace component between the presented form sheaves underlying the canonical
de Rham complexes. -/
noncomputable def presentedComponent (r : TraceRule.{u}) {X Y : Scheme.{u}}
    (f : Y ⟶ X) [IsFinite f] [Syntomic f] (p : ℕ) :
    (Scheme.Modules.pushforward f).obj
        ((Scheme.Modules.fromRingedSpace Y).obj
          (RingedSpace.DeRham.form (terminal.from Y).toLRSHom.toShHom p)) ⟶
      (Scheme.Modules.fromRingedSpace X).obj
        (RingedSpace.DeRham.form (terminal.from X).toLRSHom.toShHom p) :=
  (Scheme.Modules.pushforward f).map
      ((Scheme.Modules.fromRingedSpace Y).map
        (Scheme.DeRham.Gysin.formToExterior (terminal.from Y) p)) ≫
    r.component f p ≫
    (Scheme.Modules.fromRingedSpace X).map
      (formExteriorIso (terminal.from X) p).inv

/-- The degree-`p` trace component transported to the coefficient-module categories of the
absolute de Rham complexes. -/
noncomputable def componentTerm (r : TraceRule.{u}) {X Y : Scheme.{u}}
    (f : Y ⟶ X) [IsFinite f] [Syntomic f] (p : ℕ) :
    ((RingedSpace.DeRham.pushforwardComplex (absoluteRingedSquare f)).obj
      (RingedSpace.DeRham.complex (terminal.from Y).toLRSHom.toShHom)).X p ⟶
        (RingedSpace.DeRham.complex (terminal.from X).toLRSHom.toShHom).X p :=
  (componentSourceIso f p).hom ≫
    (DeRham.restriction
      (RingedSpace.DeRham.structureMap (terminal.from X).toLRSHom.toShHom)).map
        ((Scheme.Modules.toRingedSpace X).map (presentedComponent r f p))

/-- The transported degreewise component is the canonical restriction/pushforward comparison
followed by the original trace component. -/
theorem componentTerm_def (r : TraceRule.{u}) {X Y : Scheme.{u}}
    (f : Y ⟶ X) [IsFinite f] [Syntomic f] (p : ℕ) :
    componentTerm r f p =
      (componentSourceIso f p).hom ≫
        (DeRham.restriction
          (RingedSpace.DeRham.structureMap (terminal.from X).toLRSHom.toShHom)).map
            ((Scheme.Modules.toRingedSpace X).map
              (presentedComponent r f p)) := rfl

end TraceRule

namespace IsTraceRule

/-- Transported trace components commute with the absolute de Rham differentials. -/
theorem componentTerm_comm {r : TraceRule.{u}} (hr : IsTraceRule r)
    {X Y : Scheme.{u}} (f : Y ⟶ X) [IsFinite f] [Syntomic f]
    (i j : ℕ) (hij : (up ℕ).Rel i j) :
    TraceRule.componentTerm r f i ≫
        (RingedSpace.DeRham.complex (terminal.from X).toLRSHom.toShHom).d i j =
      ((RingedSpace.DeRham.pushforwardComplex
        (TraceRule.absoluteRingedSquare f)).obj
          (RingedSpace.DeRham.complex (terminal.from Y).toLRSHom.toShHom)).d i j ≫
        TraceRule.componentTerm r f j := sorry

end IsTraceRule

namespace TraceRule

/-- The degreewise finite-syntomic trace maps assemble into a
morphism from the pushed-forward absolute de Rham complex of `Y` to that of `X`. -/
noncomputable def complexMap (r : TraceRule.{u}) (hr : IsTraceRule r)
    {X Y : Scheme.{u}} (f : Y ⟶ X) [IsFinite f] [Syntomic f] :
    (RingedSpace.DeRham.pushforwardComplex (absoluteRingedSquare f)).obj
        (RingedSpace.DeRham.complex (terminal.from Y).toLRSHom.toShHom) ⟶
      RingedSpace.DeRham.complex (terminal.from X).toLRSHom.toShHom where
  f p := componentTerm r f p
  comm' i j hij := IsTraceRule.componentTerm_comm hr f i j hij

/-- The degree-`p` component of the absolute trace complex morphism is the transported
degreewise trace component. -/
theorem complexMap_f (r : TraceRule.{u}) (hr : IsTraceRule r)
    {X Y : Scheme.{u}} (f : Y ⟶ X) [IsFinite f] [Syntomic f] (p : ℕ) :
    (complexMap r hr f).f p = componentTerm r f p := rfl

/-- After the canonical degree-zero form identifications, the
degree-zero component of the absolute de Rham trace is the structure-sheaf trace. -/
theorem degreeZero {r : TraceRule.{u}} (hr : IsTraceRule r)
    {X Y : Scheme.{u}} (f : Y ⟶ X) [IsFinite f] [Syntomic f] :
    (complexMap r hr f).f 0 =
      (componentSourceIso f 0).hom ≫
        (DeRham.restriction
          (RingedSpace.DeRham.structureMap
            (terminal.from X).toLRSHom.toShHom)).map
          ((Scheme.Modules.toRingedSpace X).map
            ((Scheme.Modules.pushforward f).map
                  ((Scheme.Modules.fromRingedSpace Y).map
                    ((formExteriorIso (terminal.from Y) 0).hom ≫
                      (ExteriorPower.degreeZeroIso
                        Y.sheaf Ω[(terminal.from Y).toShHom]).hom)) ≫
              Scheme.Hom.finiteSyntomicTrace f ≫
              (Scheme.Modules.fromRingedSpace X).map
                ((ExteriorPower.degreeZeroIso
                    X.sheaf Ω[(terminal.from X).toShHom]).inv ≫
                  (formExteriorIso (terminal.from X) 0).inv))) := sorry

/-- Left wedge multiplication by an absolute form on `X`, acting on pushed-forward absolute
forms from `Y`. -/
noncomputable def pushforwardWedge {X Y : Scheme.{u}} (f : Y ⟶ X)
    (q p : ℕ) :
    (Λ[q] Ω[(terminal.from X).toShHom]) ⊗
        (Scheme.Modules.pushforward f).obj
          (Λ[p] Ω[(terminal.from Y).toShHom]) ⟶
      (Scheme.Modules.pushforward f).obj
        (Λ[q + p] Ω[(terminal.from Y).toShHom]) :=
  (Scheme.Modules.pullbackPushforwardAdjunction f).projectionFormulaMateOfIso
      (Scheme.Modules.pullbackTensorIso f)
      (Λ[q] Ω[(terminal.from X).toShHom])
      (Λ[p] Ω[(terminal.from Y).toShHom]) ≫
    (Scheme.Modules.pushforward f).map
      ((absoluteFormComparison f q ⊗ₘ
          𝟙 (Λ[p] Ω[(terminal.from Y).toShHom])) ≫
        ExteriorPower.mul Y.sheaf
          Ω[(terminal.from Y).toShHom] q p)

/-- The pushed-forward wedge action is the projection-formula comparison followed by wedge
multiplication on `Y`. -/
theorem pushforwardWedge_def {X Y : Scheme.{u}} (f : Y ⟶ X)
    (q p : ℕ) :
    pushforwardWedge f q p =
      (Scheme.Modules.pullbackPushforwardAdjunction f).projectionFormulaMateOfIso
          (Scheme.Modules.pullbackTensorIso f)
          (Λ[q] Ω[(terminal.from X).toShHom])
          (Λ[p] Ω[(terminal.from Y).toShHom]) ≫
        (Scheme.Modules.pushforward f).map
          ((absoluteFormComparison f q ⊗ₘ
              𝟙 (Λ[p] Ω[(terminal.from Y).toShHom])) ≫
            ExteriorPower.mul Y.sheaf
              Ω[(terminal.from Y).toShHom] q p) := rfl

/-- A trace rule is linear for left wedge multiplication when its homogeneous components
intertwine the pushed-forward and target wedge actions. -/
def IsWedgeLinear (r : TraceRule.{u}) {X Y : Scheme.{u}}
    (f : Y ⟶ X) [IsFinite f] [Syntomic f] : Prop :=
  ∀ q p : ℕ,
    pushforwardWedge f q p ≫ r.component f (q + p) =
      (𝟙 (Λ[q] Ω[(terminal.from X).toShHom]) ⊗ₘ r.component f p) ≫
        ExteriorPower.mul X.sheaf
          Ω[(terminal.from X).toShHom] q p

/-- Wedge linearity is exactly its family of homogeneous morphism equalities. -/
theorem isWedgeLinear_iff (r : TraceRule.{u}) {X Y : Scheme.{u}}
    (f : Y ⟶ X) [IsFinite f] [Syntomic f] :
    IsWedgeLinear r f ↔
      ∀ q p : ℕ,
        pushforwardWedge f q p ≫ r.component f (q + p) =
          (𝟙 (Λ[q] Ω[(terminal.from X).toShHom]) ⊗ₘ r.component f p) ≫
            ExteriorPower.mul X.sheaf
              Ω[(terminal.from X).toShHom] q p := Iff.rfl

end TraceRule

namespace IsTraceRule

/-- The finite-syntomic trace is linear for left wedge
multiplication by absolute forms on the target. -/
theorem wedge {r : TraceRule.{u}} (hr : IsTraceRule r)
    {X Y : Scheme.{u}} (f : Y ⟶ X) [IsFinite f] [Syntomic f] :
    TraceRule.IsWedgeLinear r f := sorry

end IsTraceRule


namespace TraceRule

/-- For a finite morphism, pushforward preserves the canonical exterior-form quotient from
absolute forms to forms relative to a common base. -/
theorem pushforwardAbsoluteToRelativeForm_epi
    {S X Y : Scheme.{u}} (f : Y ⟶ X) [IsFinite f] [Syntomic f]
    (a : Y ⟶ S) (p : ℕ) :
    Epi ((Scheme.Modules.pushforward f).map (absoluteToRelativeForm a p)) := sorry

/-- Wedge linearity makes the absolute trace vanish on the kernel of the canonical quotient to
relative exterior-power forms. -/
theorem relativeExteriorComponent_kernel (r : TraceRule.{u}) (hr : IsTraceRule r)
    {S X Y : Scheme.{u}} (f : Y ⟶ X) [IsFinite f] [Syntomic f]
    (a : Y ⟶ S) (b : X ⟶ S) (sq : CommSq f a b (𝟙 S)) (p : ℕ) :
    kernel.ι ((Scheme.Modules.pushforward f).map (absoluteToRelativeForm a p)) ≫
        (r.component f p ≫ absoluteToRelativeForm b p) = 0 := sorry

/-- The degree-`p` trace on relative exterior-power forms, constructed by the canonical
abelian quotient descent from the absolute trace component. -/
noncomputable def relativeExteriorComponent (r : TraceRule.{u}) (hr : IsTraceRule r)
    {S X Y : Scheme.{u}} (f : Y ⟶ X) [IsFinite f] [Syntomic f]
    (a : Y ⟶ S) (b : X ⟶ S) (sq : CommSq f a b (𝟙 S)) (p : ℕ) :
    (Scheme.Modules.pushforward f).obj (Λ[p] Ω[a.toShHom]) ⟶
      Λ[p] Ω[b.toShHom] :=
  @Abelian.epiDesc _ _ _ _ _
    ((Scheme.Modules.pushforward f).map (absoluteToRelativeForm a p))
    (pushforwardAbsoluteToRelativeForm_epi f a p) _
    (r.component f p ≫ absoluteToRelativeForm b p)
    (relativeExteriorComponent_kernel r hr f a b sq p)

/-- The relative exterior trace is induced by the absolute trace component. -/
theorem relativeExteriorComponent_induced (r : TraceRule.{u}) (hr : IsTraceRule r)
    {S X Y : Scheme.{u}} (f : Y ⟶ X) [IsFinite f] [Syntomic f]
    (a : Y ⟶ S) (b : X ⟶ S) (sq : CommSq f a b (𝟙 S)) (p : ℕ) :
    (Scheme.Modules.pushforward f).map (absoluteToRelativeForm a p) ≫
        relativeExteriorComponent r hr f a b sq p =
      r.component f p ≫ absoluteToRelativeForm b p := sorry

/-- The descent equation uniquely determines the relative exterior trace component. -/
theorem relativeExteriorComponent_unique (r : TraceRule.{u}) (hr : IsTraceRule r)
    {S X Y : Scheme.{u}} (f : Y ⟶ X) [IsFinite f] [Syntomic f]
    (a : Y ⟶ S) (b : X ⟶ S) (sq : CommSq f a b (𝟙 S)) (p : ℕ)
    (φ : (Scheme.Modules.pushforward f).obj (Λ[p] Ω[a.toShHom]) ⟶
      Λ[p] Ω[b.toShHom])
    (hφ : (Scheme.Modules.pushforward f).map (absoluteToRelativeForm a p) ≫ φ =
      r.component f p ≫ absoluteToRelativeForm b p) :
    φ = relativeExteriorComponent r hr f a b sq p := sorry

end TraceRule

namespace IsTraceRule

/-- A valid absolute trace rule has a unique degreewise descent to relative exterior-power
forms over every common base. -/
theorem existsUniqueRelativeExteriorComponent {r : TraceRule.{u}}
    (hr : IsTraceRule r) {S X Y : Scheme.{u}}
    (f : Y ⟶ X) [IsFinite f] [Syntomic f]
    (a : Y ⟶ S) (b : X ⟶ S) (sq : CommSq f a b (𝟙 S)) (p : ℕ) :
    ∃! φ : (Scheme.Modules.pushforward f).obj (Λ[p] Ω[a.toShHom]) ⟶
        Λ[p] Ω[b.toShHom],
      (Scheme.Modules.pushforward f).map (absoluteToRelativeForm a p) ≫ φ =
        r.component f p ≫ absoluteToRelativeForm b p := sorry

end IsTraceRule

namespace TraceRule

/-- The relative square regarded as a square of underlying ringed spaces. -/
abbrev relativeRingedSquare {S X Y : Scheme.{u}}
    {f : Y ⟶ X} {a : Y ⟶ S} {b : X ⟶ S} (sq : CommSq f a b (𝟙 S)) :=
  sq.map (Scheme.forgetToLocallyRingedSpace ⋙ LocallyRingedSpace.forgetToSheafedSpace)

/-- The structure map of a relative coefficient square agrees with the restriction of the
usual structure-sheaf map. -/
theorem relativeStructureMap {S X Y : Scheme.{u}}
    (f : Y ⟶ X) (a : Y ⟶ S) (b : X ⟶ S) (sq : CommSq f a b (𝟙 S)) :
    (RingedSpace.DeRham.baseChangeHom (relativeRingedSquare sq)).structureSheafMap ≫
        ((Opens.map f.base).sheafPushforwardContinuous
          RingCat (Opens.grothendieckTopology X)
            (Opens.grothendieckTopology Y)).map
            (TopCat.Sheaf.ringSheafOfCommMap
              (RingedSpace.DeRham.structureMap a.toLRSHom.toShHom)) =
      TopCat.Sheaf.ringSheafOfCommMap
          (RingedSpace.DeRham.structureMap b.toLRSHom.toShHom) ≫
        RingedSpace.Hom.toRingCatSheafHom f.toLRSHom.toShHom := sorry

/-- Coefficient pushforward of a relative form is canonically scalar restriction of its usual
scheme-theoretic pushforward. -/
noncomputable def relativeComponentSourceIso {S X Y : Scheme.{u}}
    (f : Y ⟶ X) (a : Y ⟶ S) (b : X ⟶ S)
    (sq : CommSq f a b (𝟙 S)) (p : ℕ) :
    (RingedSpace.DeRham.pushforward (relativeRingedSquare sq)).obj
        (RingedSpace.DeRham.term a.toLRSHom.toShHom p) ≅
      (DeRham.restriction
        (RingedSpace.DeRham.structureMap b.toLRSHom.toShHom)).obj
          ((Scheme.Modules.toRingedSpace X).obj
            ((Scheme.Modules.pushforward f).obj
              ((Scheme.Modules.fromRingedSpace Y).obj
                (RingedSpace.DeRham.form a.toLRSHom.toShHom p)))) :=
  (SheafOfModules.restrictPushforwardIso
      (F := Opens.map f.base) (J := Opens.grothendieckTopology X)
      (K := Opens.grothendieckTopology Y)
      (TopCat.Sheaf.ringSheafOfCommMap
        (RingedSpace.DeRham.structureMap a.toLRSHom.toShHom))
      (RingedSpace.DeRham.baseChangeHom (relativeRingedSquare sq)).structureSheafMap
      (TopCat.Sheaf.ringSheafOfCommMap
          (RingedSpace.DeRham.structureMap b.toLRSHom.toShHom) ≫
        RingedSpace.Hom.toRingCatSheafHom f.toLRSHom.toShHom)
      (relativeStructureMap f a b sq)).app
        (RingedSpace.DeRham.form a.toLRSHom.toShHom p) ≪≫
    (SheafOfModules.pushforwardRestrictIso
      (F := Opens.map f.base) (J := Opens.grothendieckTopology X)
      (K := Opens.grothendieckTopology Y)
      (TopCat.Sheaf.ringSheafOfCommMap
        (RingedSpace.DeRham.structureMap b.toLRSHom.toShHom))
      (RingedSpace.Hom.toRingCatSheafHom f.toLRSHom.toShHom)).symm.app
        (RingedSpace.DeRham.form a.toLRSHom.toShHom p)

/-- The canonical absolute-to-relative comparison on pushed-forward de Rham terms after
forgetting their coefficient-module structures. -/
noncomputable def absoluteToRelativeSourceTerm {S X Y : Scheme.{u}}
    (f : Y ⟶ X) (a : Y ⟶ S) (b : X ⟶ S)
    (sq : CommSq f a b (𝟙 S)) (p : ℕ) :
    (SheafOfModules.toSheaf
        (TopCat.Sheaf.ringSheafOfComm
          (RingedSpace.DeRham.coefficients
            (terminal.from X).toLRSHom.toShHom))).obj
        (((RingedSpace.DeRham.pushforwardComplex (absoluteRingedSquare f)).obj
          (RingedSpace.DeRham.complex
            (terminal.from Y).toLRSHom.toShHom)).X p) ⟶
      (SheafOfModules.toSheaf
        (TopCat.Sheaf.ringSheafOfComm
          (RingedSpace.DeRham.coefficients b.toLRSHom.toShHom))).obj
        (((RingedSpace.DeRham.pushforwardComplex (relativeRingedSquare sq)).obj
          (RingedSpace.DeRham.complex a.toLRSHom.toShHom)).X p) :=
  (SheafOfModules.toSheaf
      (TopCat.Sheaf.ringSheafOfComm
        (RingedSpace.DeRham.coefficients
          (terminal.from X).toLRSHom.toShHom))).map
      (componentSourceIso f p).hom ≫
    (SheafOfModules.toSheaf
      (TopCat.Sheaf.ringSheafOfComm
        (RingedSpace.DeRham.coefficients
          (terminal.from X).toLRSHom.toShHom))).map
      ((DeRham.restriction
        (RingedSpace.DeRham.structureMap
          (terminal.from X).toLRSHom.toShHom)).map
        ((Scheme.Modules.toRingedSpace X).map
          ((Scheme.Modules.pushforward f).map
            ((Scheme.Modules.fromRingedSpace Y).map
              ((formExteriorIso (terminal.from Y) p).hom ≫
                absoluteToRelativeForm a p ≫ (formExteriorIso a p).inv))))) ≫
    (SheafOfModules.toSheaf
      (TopCat.Sheaf.ringSheafOfComm
        (RingedSpace.DeRham.coefficients b.toLRSHom.toShHom))).map
      (relativeComponentSourceIso f a b sq p).inv

/-- The relative trace component between the presented form sheaves underlying the canonical
relative de Rham complexes. -/
noncomputable def relativePresentedComponent (r : TraceRule.{u}) (hr : IsTraceRule r)
    {S X Y : Scheme.{u}} (f : Y ⟶ X) [IsFinite f] [Syntomic f]
    (a : Y ⟶ S) (b : X ⟶ S) (sq : CommSq f a b (𝟙 S)) (p : ℕ) :
    (Scheme.Modules.pushforward f).obj
        ((Scheme.Modules.fromRingedSpace Y).obj
          (RingedSpace.DeRham.form a.toLRSHom.toShHom p)) ⟶
      (Scheme.Modules.fromRingedSpace X).obj
        (RingedSpace.DeRham.form b.toLRSHom.toShHom p) :=
  (Scheme.Modules.pushforward f).map
      ((Scheme.Modules.fromRingedSpace Y).map (Scheme.DeRham.Gysin.formToExterior a p)) ≫
    relativeExteriorComponent r hr f a b sq p ≫
    (Scheme.Modules.fromRingedSpace X).map (formExteriorIso b p).inv

/-- The degreewise relative trace, transported to the coefficient-module categories of the
relative de Rham complexes. -/
noncomputable def relativeComponent (r : TraceRule.{u}) (hr : IsTraceRule r)
    {S X Y : Scheme.{u}} (f : Y ⟶ X) [IsFinite f] [Syntomic f]
    (a : Y ⟶ S) (b : X ⟶ S) (sq : CommSq f a b (𝟙 S)) (p : ℕ) :
    ((RingedSpace.DeRham.pushforwardComplex (relativeRingedSquare sq)).obj
      (RingedSpace.DeRham.complex a.toLRSHom.toShHom)).X p ⟶
        (RingedSpace.DeRham.complex b.toLRSHom.toShHom).X p :=
  (relativeComponentSourceIso f a b sq p).hom ≫
    (DeRham.restriction
      (RingedSpace.DeRham.structureMap b.toLRSHom.toShHom)).map
        ((Scheme.Modules.toRingedSpace X).map
          (relativePresentedComponent r hr f a b sq p))

/-- The relative presented trace is induced degreewise from the absolute presented trace. -/
theorem relativeComponent_induced (r : TraceRule.{u}) (hr : IsTraceRule r)
    {S X Y : Scheme.{u}} (f : Y ⟶ X) [IsFinite f] [Syntomic f]
    (a : Y ⟶ S) (b : X ⟶ S) (sq : CommSq f a b (𝟙 S)) (p : ℕ) :
    (Scheme.Modules.pushforward f).map
          ((Scheme.Modules.fromRingedSpace Y).map
            ((formExteriorIso (terminal.from Y) p).hom ≫
              absoluteToRelativeForm a p ≫ (formExteriorIso a p).inv)) ≫
        relativePresentedComponent r hr f a b sq p =
      presentedComponent r f p ≫
        (Scheme.Modules.fromRingedSpace X).map
          ((formExteriorIso (terminal.from X) p).hom ≫
            absoluteToRelativeForm b p ≫ (formExteriorIso b p).inv) := sorry

end TraceRule

namespace IsTraceRule

/-- Relative trace components commute with relative de Rham differentials. -/
theorem relativeComponent_comm {r : TraceRule.{u}} (hr : IsTraceRule r)
    {S X Y : Scheme.{u}} (f : Y ⟶ X) [IsFinite f] [Syntomic f]
    (a : Y ⟶ S) (b : X ⟶ S) (sq : CommSq f a b (𝟙 S))
    (i j : ℕ) (hij : (up ℕ).Rel i j) :
    TraceRule.relativeComponent r hr f a b sq i ≫
        (RingedSpace.DeRham.complex b.toLRSHom.toShHom).d i j =
      ((RingedSpace.DeRham.pushforwardComplex
        (TraceRule.relativeRingedSquare sq)).obj
          (RingedSpace.DeRham.complex a.toLRSHom.toShHom)).d i j ≫
        TraceRule.relativeComponent r hr f a b sq j := sorry

end IsTraceRule

namespace TraceRule

/-- For a finite syntomic morphism over `S`, the absolute trace
induces a morphism from the pushed-forward relative de Rham complex of `Y/S` to that of `X/S`. -/
noncomputable def relativeComplexMap (r : TraceRule.{u}) (hr : IsTraceRule r)
    {S X Y : Scheme.{u}} (f : Y ⟶ X) [IsFinite f] [Syntomic f]
    (a : Y ⟶ S) (b : X ⟶ S) (sq : CommSq f a b (𝟙 S)) :
    (RingedSpace.DeRham.pushforwardComplex (relativeRingedSquare sq)).obj
        (RingedSpace.DeRham.complex a.toLRSHom.toShHom) ⟶
      RingedSpace.DeRham.complex b.toLRSHom.toShHom where
  f p := relativeComponent r hr f a b sq p
  comm' i j hij := IsTraceRule.relativeComponent_comm hr f a b sq i j hij

/-- The degree-`p` component of the relative trace complex morphism is the descended trace
component. -/
theorem relativeComplexMap_f (r : TraceRule.{u}) (hr : IsTraceRule r)
    {S X Y : Scheme.{u}} (f : Y ⟶ X) [IsFinite f] [Syntomic f]
    (a : Y ⟶ S) (b : X ⟶ S) (sq : CommSq f a b (𝟙 S)) (p : ℕ) :
    (relativeComplexMap r hr f a b sq).f p =
      relativeComponent r hr f a b sq p := rfl

/-- After forgetting coefficient-module structures, the degree-`p` components of the absolute
and relative bundled trace maps form the canonical absolute-to-relative commutative square. -/
theorem relativeComplexMap_induced (r : TraceRule.{u}) (hr : IsTraceRule r)
    {S X Y : Scheme.{u}} (f : Y ⟶ X) [IsFinite f] [Syntomic f]
    (a : Y ⟶ S) (b : X ⟶ S) (sq : CommSq f a b (𝟙 S)) (p : ℕ) :
    absoluteToRelativeSourceTerm f a b sq p ≫
        (SheafOfModules.toSheaf
          (TopCat.Sheaf.ringSheafOfComm
            (RingedSpace.DeRham.coefficients b.toLRSHom.toShHom))).map
          ((relativeComplexMap r hr f a b sq).f p) =
      (SheafOfModules.toSheaf
        (TopCat.Sheaf.ringSheafOfComm
          (RingedSpace.DeRham.coefficients
            (terminal.from X).toLRSHom.toShHom))).map
          ((complexMap r hr f).f p) ≫
        absoluteToRelativeTerm b p := sorry

end TraceRule

end AlgebraicGeometry.Scheme.RelativeDifferentials
