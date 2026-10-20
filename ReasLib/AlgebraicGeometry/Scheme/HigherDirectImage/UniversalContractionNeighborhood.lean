module

public import ReasLib.AlgebraicGeometry.Scheme.HigherDirectImage.ContractionNeighborhood
public import ReasLib.AlgebraicGeometry.Scheme.HigherDirectImage.StructureSheafFlatBaseChange

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open scoped AlgebraicGeometry

noncomputable section

namespace AlgebraicGeometry.Scheme.HigherDirectImage

/-- An open neighbourhood on which flatness, the fibre-dimension bound,
degree-one vanishing, and the structure-sheaf isomorphism hold, universally
after base change over the base scheme. -/
structure UniversalContractionNeighborhood.{u} {X Y S : Scheme.{u}}
    (p : X ⟶ S) (q : Y ⟶ S) (f : X ⟶ Y) (s : S) where
  /-- The chosen open neighbourhood in `Y`. -/
  openSet : Y.Opens
  /-- Every point of the fibre `Yₛ` belongs to the chosen open. -/
  containsFiber : ∀ yₛ : q.fiber s, q.fiberι s yₛ ∈ openSet
  /-- The chosen open is flat over `S`. -/
  flatTargetOverBase : Flat (openSet.ι ≫ q)
  /-- The inverse image of the chosen open is flat over `S`. -/
  flatSourceOverBase : Flat ((f ⁻¹ᵁ openSet).ι ≫ p)
  /-- The fibres of the restricted morphism have dimension at most one. -/
  fiberDimensionLEOne : ∀ y : openSet,
    topologicalKrullDim ((f ∣_ openSet).fiber y) ≤ (1 : WithBot ℕ∞)
  /-- The restriction of `R¹ f_* 𝒪_X` to the chosen open vanishes. -/
  degreeOneIsZero : IsZero
    ((RingedSpace.Hom.higherDirectImageModule f.toShHom
      (SheafOfModules.unit X.ringCatSheaf) 1).over openSet)
  /-- The structure-sheaf map for the restricted morphism is an isomorphism. -/
  structureSheafMapIsIso : IsIso
    (RingedSpace.Hom.commRingSheafPushforwardMap (f ∣_ openSet).toShHom)
  /-- Every base change of the chosen open along a morphism `S' ⟶ S` is flat over `S'`. -/
  baseChangeFlatTargetOverBase :
    ∀ {Y' S' : Scheme.{u}} (g : S' ⟶ S)
      (gY : Y' ⟶ openSet) (q' : Y' ⟶ S'),
      IsPullback gY q' (openSet.ι ≫ q) g → Flat q'
  /-- The base-changed inverse image is flat over the new base scheme. -/
  baseChangeFlatSourceOverBase :
    ∀ {X' Y' S' : Scheme.{u}} (g : S' ⟶ S)
      (gY : Y' ⟶ openSet) (q' : Y' ⟶ S'),
      IsPullback gY q' (openSet.ι ≫ q) g →
        ∀ (gX : X' ⟶ (f ⁻¹ᵁ openSet).toScheme) (f' : X' ⟶ Y'),
          IsPullback gX f' (f ∣_ openSet) gY → Flat (f' ≫ q')
  /-- The fibre-dimension bound persists after every base change over `S`. -/
  baseChangeFiberDimensionLEOne :
    ∀ {X' Y' S' : Scheme.{u}} (g : S' ⟶ S)
      (gY : Y' ⟶ openSet) (q' : Y' ⟶ S'),
      IsPullback gY q' (openSet.ι ≫ q) g →
        ∀ (gX : X' ⟶ (f ⁻¹ᵁ openSet).toScheme) (f' : X' ⟶ Y'),
          IsPullback gX f' (f ∣_ openSet) gY →
            ∀ y' : Y', topologicalKrullDim (f'.fiber y') ≤ (1 : WithBot ℕ∞)
  /-- Degree-one higher-direct-image vanishing persists after every base change over `S`. -/
  baseChangeDegreeOneIsZero :
    ∀ {X' Y' S' : Scheme.{u}} (g : S' ⟶ S)
      (gY : Y' ⟶ openSet) (q' : Y' ⟶ S'),
      IsPullback gY q' (openSet.ι ≫ q) g →
        ∀ (gX : X' ⟶ (f ⁻¹ᵁ openSet).toScheme) (f' : X' ⟶ Y'),
          IsPullback gX f' (f ∣_ openSet) gY →
            IsZero (RingedSpace.Hom.higherDirectImageModule f'.toShHom
              (SheafOfModules.unit X'.ringCatSheaf) 1)
  /-- The structure-sheaf map remains an isomorphism after every base change over `S`. -/
  baseChangeStructureSheafMapIsIso :
    ∀ {X' Y' S' : Scheme.{u}} (g : S' ⟶ S)
      (gY : Y' ⟶ openSet) (q' : Y' ⟶ S'),
      IsPullback gY q' (openSet.ι ≫ q) g →
        ∀ (gX : X' ⟶ (f ⁻¹ᵁ openSet).toScheme) (f' : X' ⟶ Y'),
          IsPullback gX f' (f ∣_ openSet) gY → IsIso
            (RingedSpace.Hom.commRingSheafPushforwardMap f'.toShHom)

universe u

variable {X Y S : Scheme.{u}}

namespace UniversalContractionNeighborhood

/-- Upgrade a contraction neighbourhood once target flatness and the direct and
base-changed structure-sheaf isomorphisms and flatness facts are available. -/
def ofContractionNeighborhood (p : X ⟶ S) (q : Y ⟶ S) (f : X ⟶ Y) (s : S)
    (N : ContractionNeighborhood p q f s)
    (flatTargetOverBase : Flat (N.openSet.ι ≫ q))
    (structureSheafMapIsIso : IsIso
      (RingedSpace.Hom.commRingSheafPushforwardMap (f ∣_ N.openSet).toShHom))
    (baseChangeFlatTargetOverBase :
      ∀ {Y' S' : Scheme.{u}} (g : S' ⟶ S)
        (gY : Y' ⟶ N.openSet) (q' : Y' ⟶ S'),
        IsPullback gY q' (N.openSet.ι ≫ q) g → Flat q')
    (baseChangeFlatSourceOverBase :
      ∀ {X' Y' S' : Scheme.{u}} (g : S' ⟶ S)
        (gY : Y' ⟶ N.openSet) (q' : Y' ⟶ S'),
        IsPullback gY q' (N.openSet.ι ≫ q) g →
          ∀ (gX : X' ⟶ (f ⁻¹ᵁ N.openSet).toScheme) (f' : X' ⟶ Y'),
            IsPullback gX f' (f ∣_ N.openSet) gY → Flat (f' ≫ q'))
    (baseChangeStructureSheafMapIsIso :
      ∀ {X' Y' S' : Scheme.{u}} (g : S' ⟶ S)
        (gY : Y' ⟶ N.openSet) (q' : Y' ⟶ S'),
        IsPullback gY q' (N.openSet.ι ≫ q) g →
          ∀ (gX : X' ⟶ (f ⁻¹ᵁ N.openSet).toScheme) (f' : X' ⟶ Y'),
            IsPullback gX f' (f ∣_ N.openSet) gY → IsIso
              (RingedSpace.Hom.commRingSheafPushforwardMap f'.toShHom)) :
    UniversalContractionNeighborhood p q f s where
  openSet := N.openSet
  containsFiber := N.containsFiber
  flatTargetOverBase := flatTargetOverBase
  flatSourceOverBase := N.flatOverBase
  fiberDimensionLEOne := N.fiberDimensionLEOne
  degreeOneIsZero := N.degreeOneIsZero
  structureSheafMapIsIso := structureSheafMapIsIso
  baseChangeFlatTargetOverBase := baseChangeFlatTargetOverBase
  baseChangeFlatSourceOverBase := baseChangeFlatSourceOverBase
  baseChangeFiberDimensionLEOne := fun _ _ _ _ gX f' hf ↦
    N.baseChangeFiberDimensionLEOne gX f' _ hf
  baseChangeDegreeOneIsZero := fun _ _ _ _ gX f' hf ↦
    N.baseChangeDegreeOneIsZero gX f' _ hf
  baseChangeStructureSheafMapIsIso := baseChangeStructureSheafMapIsIso

/-- All defining direct and base-change-stable properties of a universal
contraction neighbourhood. -/
theorem spec (p : X ⟶ S) (q : Y ⟶ S) (f : X ⟶ Y) (s : S)
    (N : UniversalContractionNeighborhood p q f s) :
    (∀ yₛ : q.fiber s, q.fiberι s yₛ ∈ N.openSet) ∧
      Flat (N.openSet.ι ≫ q) ∧
      Flat ((f ⁻¹ᵁ N.openSet).ι ≫ p) ∧
      (∀ y : N.openSet,
        topologicalKrullDim ((f ∣_ N.openSet).fiber y) ≤ (1 : WithBot ℕ∞)) ∧
      IsZero ((RingedSpace.Hom.higherDirectImageModule f.toShHom
        (SheafOfModules.unit X.ringCatSheaf) 1).over N.openSet) ∧
      IsIso (RingedSpace.Hom.commRingSheafPushforwardMap
        (f ∣_ N.openSet).toShHom) ∧
      (∀ {Y' S' : Scheme.{u}} (g : S' ⟶ S)
        (gY : Y' ⟶ N.openSet) (q' : Y' ⟶ S'),
        IsPullback gY q' (N.openSet.ι ≫ q) g → Flat q') ∧
      (∀ {X' Y' S' : Scheme.{u}} (g : S' ⟶ S)
        (gY : Y' ⟶ N.openSet) (q' : Y' ⟶ S'),
        IsPullback gY q' (N.openSet.ι ≫ q) g →
          ∀ (gX : X' ⟶ (f ⁻¹ᵁ N.openSet).toScheme) (f' : X' ⟶ Y'),
            IsPullback gX f' (f ∣_ N.openSet) gY → Flat (f' ≫ q')) ∧
      (∀ {X' Y' S' : Scheme.{u}} (g : S' ⟶ S)
        (gY : Y' ⟶ N.openSet) (q' : Y' ⟶ S'),
        IsPullback gY q' (N.openSet.ι ≫ q) g →
          ∀ (gX : X' ⟶ (f ⁻¹ᵁ N.openSet).toScheme) (f' : X' ⟶ Y'),
            IsPullback gX f' (f ∣_ N.openSet) gY →
              ∀ y' : Y', topologicalKrullDim (f'.fiber y') ≤ (1 : WithBot ℕ∞)) ∧
      (∀ {X' Y' S' : Scheme.{u}} (g : S' ⟶ S)
        (gY : Y' ⟶ N.openSet) (q' : Y' ⟶ S'),
        IsPullback gY q' (N.openSet.ι ≫ q) g →
          ∀ (gX : X' ⟶ (f ⁻¹ᵁ N.openSet).toScheme) (f' : X' ⟶ Y'),
            IsPullback gX f' (f ∣_ N.openSet) gY →
              IsZero (RingedSpace.Hom.higherDirectImageModule f'.toShHom
                (SheafOfModules.unit X'.ringCatSheaf) 1)) ∧
      (∀ {X' Y' S' : Scheme.{u}} (g : S' ⟶ S)
        (gY : Y' ⟶ N.openSet) (q' : Y' ⟶ S'),
        IsPullback gY q' (N.openSet.ι ≫ q) g →
          ∀ (gX : X' ⟶ (f ⁻¹ᵁ N.openSet).toScheme) (f' : X' ⟶ Y'),
            IsPullback gX f' (f ∣_ N.openSet) gY → IsIso
              (RingedSpace.Hom.commRingSheafPushforwardMap f'.toShHom)) := sorry

/-- Upgrading a contraction neighbourhood retains its chosen open. -/
theorem ofContractionNeighborhood_openSet (p : X ⟶ S) (q : Y ⟶ S) (f : X ⟶ Y)
    (s : S) (N : ContractionNeighborhood p q f s)
    (flatTargetOverBase : Flat (N.openSet.ι ≫ q))
    (structureSheafMapIsIso : IsIso
      (RingedSpace.Hom.commRingSheafPushforwardMap (f ∣_ N.openSet).toShHom))
    (baseChangeFlatTargetOverBase :
      ∀ {Y' S' : Scheme.{u}} (g : S' ⟶ S)
        (gY : Y' ⟶ N.openSet) (q' : Y' ⟶ S'),
        IsPullback gY q' (N.openSet.ι ≫ q) g → Flat q')
    (baseChangeFlatSourceOverBase :
      ∀ {X' Y' S' : Scheme.{u}} (g : S' ⟶ S)
        (gY : Y' ⟶ N.openSet) (q' : Y' ⟶ S'),
        IsPullback gY q' (N.openSet.ι ≫ q) g →
          ∀ (gX : X' ⟶ (f ⁻¹ᵁ N.openSet).toScheme) (f' : X' ⟶ Y'),
            IsPullback gX f' (f ∣_ N.openSet) gY → Flat (f' ≫ q'))
    (baseChangeStructureSheafMapIsIso :
      ∀ {X' Y' S' : Scheme.{u}} (g : S' ⟶ S)
        (gY : Y' ⟶ N.openSet) (q' : Y' ⟶ S'),
        IsPullback gY q' (N.openSet.ι ≫ q) g →
          ∀ (gX : X' ⟶ (f ⁻¹ᵁ N.openSet).toScheme) (f' : X' ⟶ Y'),
            IsPullback gX f' (f ∣_ N.openSet) gY → IsIso
              (RingedSpace.Hom.commRingSheafPushforwardMap f'.toShHom)) :
    (ofContractionNeighborhood p q f s N flatTargetOverBase structureSheafMapIsIso
      baseChangeFlatTargetOverBase baseChangeFlatSourceOverBase
      baseChangeStructureSheafMapIsIso).openSet = N.openSet := sorry

end UniversalContractionNeighborhood

/-- The special-fibre hypotheses for a proper commutative triangle give an
open neighbourhood of `Yₛ` on which target and source flatness, the
fibre-dimension bound, degree-one vanishing, and the structure-sheaf
isomorphism hold and remain true after every base change `S' ⟶ S`. -/
@[stacks 0E7L]
theorem exists_universalContractionNeighborhood
    (p : X ⟶ S) (q : Y ⟶ S) (f : X ⟶ Y) (sq : CommSq f p q (𝟙 S)) (s : S)
    [LocallyOfFinitePresentation p]
    (hflat : ∀ xₛ : p.fiber s, p.flatAt (p.fiberι s xₛ))
    [LocallyOfFinitePresentation q] [IsProper f]
    (hdim : ∀ yₛ : q.fiber s,
      topologicalKrullDim
        ((Scheme.Hom.fiberMap p f (𝟙 S) q sq s).fiber yₛ) ≤ (1 : WithBot ℕ∞))
    (hH1 : IsZero
      (RingedSpace.Hom.higherDirectImageModule
        (Scheme.Hom.fiberMap p f (𝟙 S) q sq s).toShHom
        (SheafOfModules.unit (p.fiber s).ringCatSheaf) 1))
    [IsIso (RingedSpace.Hom.commRingSheafPushforwardMap
      (Scheme.Hom.fiberMap p f (𝟙 S) q sq s).toShHom)] :
    Nonempty (UniversalContractionNeighborhood p q f s) := sorry

end AlgebraicGeometry.Scheme.HigherDirectImage
