module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Etale.CurveComparison.CompactHomologyPairing

@[expose] public section

open CategoryTheory CategoryTheory.Action.ModuleCat

noncomputable section

universe u

namespace CompactRepresentation

variable (Λ G : Type u) [CommRing Λ] [Finite Λ]
variable [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

/-- The finite coefficient module, with its genuine compact discrete topology. -/
def finiteCompactModule (M : DiscreteModuleCat Λ G) [Finite M.obj.V] : CompactModule Λ where
  toModule := M.obj.V
  topology := ⊥
  compact := by sorry
  t2 := by sorry
  topologicalAdd := by sorry
  scalarContinuous := by sorry

/-- No change of the finite representation or of its scalar action. -/
def finiteCompactAction (M : DiscreteModuleCat Λ G) [Finite M.obj.V] :
    Action (CompactModule Λ) G where
  V := finiteCompactModule Λ G M
  ρ :=
    { toFun := fun g ↦
        { toLinearMap := (M.obj.ρ g).hom
          cont := by sorry }
      map_one' := by sorry
      map_mul' := by sorry }

def finiteCompactification (M : DiscreteModuleCat Λ G) [Finite M.obj.V] : Cat Λ G :=
  ⟨finiteCompactAction Λ G M, by sorry⟩

/-- Inclusion of continuous characters into all characters. It is invertible
HERE because the input is finite discrete, never for arbitrary compact input. -/
def finiteCharacterInclusion (M : DiscreteModuleCat Λ G) [Finite M.obj.V] :
    (continuousDual Λ G (finiteCompactification Λ G M)).obj.V →ₗ[Λ]
      CharacterModule M.obj.V :=
  (CompactModule.characters Λ (finiteCompactModule Λ G M)).subtype

theorem finiteCharacterInclusion_bijective (M : DiscreteModuleCat Λ G) [Finite M.obj.V] :
    Function.Bijective (finiteCharacterInclusion Λ G M) := by sorry

def finiteCharacterComparison (M : DiscreteModuleCat Λ G) [Finite M.obj.V] :
    (continuousDual Λ G (finiteCompactification Λ G M)).obj.V ≅
      ModuleCat.of Λ (CharacterModule M.obj.V) :=
  (LinearEquiv.ofBijective (finiteCharacterInclusion Λ G M)
    (finiteCharacterInclusion_bijective Λ G M)).toModuleIso

/-- Use an actual ambient injective resolution of the continuous dual. -/
def finiteDualResolution (M : DiscreteModuleCat Λ G) [Finite M.obj.V] :
    InjectiveResolution (continuousDual Λ G (finiteCompactification Λ G M)) :=
  (HasInjectiveResolution.out
    (Z := continuousDual Λ G (finiteCompactification Λ G M))).some

/-- The finite-input evaluation pairs actual compact homology with actual
ambient cohomology of its continuous character dual. -/
def finiteHomologyPairing (M : DiscreteModuleCat Λ G) [Finite M.obj.V] (i : ℕ)
    (x : ((continuousHomology Λ G i).obj (finiteCompactification Λ G M)).toModule)
    (c : (AmbientDiscreteCohomology.cohomology Λ G i).obj
      (continuousDual Λ G (finiteCompactification Λ G M))) : AddCircle (1 : ℚ) :=
  compactHomologyPairing Λ G (finiteCompactification Λ G M) (finiteDualResolution Λ G M) i x c

end CompactRepresentation
