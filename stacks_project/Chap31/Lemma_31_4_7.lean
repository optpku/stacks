module

import StacksCheckRecall
import ReasLib.AlgebraicGeometry.Scheme.Module.SchemeTheoreticSupport.EmbeddedPoints

open AlgebraicGeometry

universe u

/- On an affine open, the canonical scheme-theoretic support ideal is the section ideal of the
kernel annihilator sheaf. -/
#check
  (AlgebraicGeometry.Scheme.Modules.schemeTheoreticSupport_ideal_eq_annihilator_sections :
    ∀ {X : Scheme.{u}} (ℱ : X.Modules) [ℱ.IsQuasicoherent] [ℱ.IsFiniteType]
      (U : X.affineOpens),
      (Scheme.Modules.schemeTheoreticSupport ℱ).ideal U =
        SheafOfModules.RingedSite.IdealSheaf.sections
          (SheafOfModules.Annihilator.subobject (X := X.toRingedSpace) ℱ)
          (Opposite.op (U : X.Opens)))

/- The annihilator of a coherent module on a locally Noetherian scheme is coherent. -/
#check
  (AlgebraicGeometry.Scheme.Modules.instIsCoherentAnnihilator :
    ∀ {X : Scheme.{u}} [IsLocallyNoetherian X] (ℱ : X.Modules) [ℱ.IsCoherent],
      (SheafOfModules.annihilator (X := X.toRingedSpace) ℱ).IsCoherent)

/- The canonical scheme-theoretic support closed subscheme has no embedded points when the
original coherent module has no embedded associated points. -/
#check
  (AlgebraicGeometry.Scheme.Modules.embeddedPoints_schemeTheoreticSupport_subscheme_eq_empty :
    ∀ {X : Scheme.{u}} [IsLocallyNoetherian X] (ℱ : X.Modules) [ℱ.IsCoherent],
      ℱ.embeddedAssociatedPoints = (∅ : Set X) →
        (Scheme.Modules.schemeTheoreticSupport ℱ).subscheme.embeddedPoints =
          (∅ : Set (Scheme.Modules.schemeTheoreticSupport ℱ).subscheme))

/- Lemma 31.4.7: let `X` be a locally Noetherian scheme and let `ℱ` be a coherent
`𝒪_X`-module without embedded associated points. The kernel annihilator sheaf is coherent and
defines the canonical scheme-theoretic support `Z`, which has no embedded points. Moreover,
`ℱ` is the pushforward of a coherent module on `Z` without embedded associated points and with
support all of `Z`. -/
@[stacks 02OM] #check
  (AlgebraicGeometry.Scheme.Modules.exists_coherent_module_on_schemeTheoreticSupport :
    ∀ {X : Scheme.{u}} [IsLocallyNoetherian X] (ℱ : X.Modules) [ℱ.IsCoherent],
      ℱ.embeddedAssociatedPoints = (∅ : Set X) →
        ∃ 𝒢 : (Scheme.Modules.schemeTheoreticSupport ℱ).subscheme.Modules,
          ∃ _ : 𝒢.IsCoherent,
            Nonempty
                ((Scheme.Modules.pushforward
                  (Scheme.Modules.schemeTheoreticSupport ℱ).subschemeι).obj 𝒢 ≅ ℱ) ∧
              𝒢.embeddedAssociatedPoints =
                (∅ : Set (Scheme.Modules.schemeTheoreticSupport ℱ).subscheme) ∧
              RingedSpace.moduleSupport 𝒢 =
                (Set.univ : Set (Scheme.Modules.schemeTheoreticSupport ℱ).subscheme))
