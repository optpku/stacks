module

public import ReasLib.AlgebraicGeometry.Scheme.Divisor.EffectiveCartier
public import ReasLib.AlgebraicGeometry.Scheme.Module.Conormal.Algebra.Map
public import ReasLib.AlgebraicGeometry.Scheme.Module.Conormal.NormalCone.Comparison
public import ReasLib.AlgebraicGeometry.Scheme.Module.Conormal.Transitivity
public import ReasLib.AlgebraicGeometry.Scheme.QuasiCoherentAlgebra.Pushforward
public import ReasLib.AlgebraicGeometry.Scheme.RelativeSpectrum.Properties
public import ReasLib.AlgebraicGeometry.Scheme.VectorBundle.LineBundle.ZeroSection
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.Graded.Map

/-!
# Normal cones for nested effective Cartier divisors

This file supplies the canonical maps from the normal cone of a composite immersion to the
normal bundle of the outer immersion and from the relative normal cone to the ambient normal
cone. It constructs the zero-section fiber and its canonical relative-cone comparison.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open SheafOfModules.RingedSite

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.NormalCone

variable {S X Y Z : Scheme.{u}}

/-- The module underlying the pushed-forward structure-sheaf algebra is the ordinary
pushforward of the structure module. -/
noncomputable def pushforwardStructureModuleIso (f : X ⟶ S)
    [QuasiCompact f] [QuasiSeparated f] :
    QcAlgebraUnder.underlyingModule S (pushforwardStructureSheafQcAlgebra f) ≅
      (Modules.pushforward f).obj
        (unitModule (Opens.grothendieckTopology X) X.sheaf) :=
  Iso.refl _

/-- The normal cone of `i` regarded as a scheme over a further base `S`. -/
noncomputable def over (p : Z ⟶ S) (i : Z ⟶ X) [IsImmersion i]
    (P : RelativeSpectrumOver (ConormalAlgebra.total i)) [IsRelativeSpectrumOver P] :
    Over S :=
  Over.mk (normalConeπ i P ≫ p)

/-- The structure morphism of a normal cone over a further base is the normal-cone
projection followed by the given map to that base. -/
theorem over_hom (p : Z ⟶ S) (i : Z ⟶ X) [IsImmersion i]
    (P : RelativeSpectrumOver (ConormalAlgebra.total i)) [IsRelativeSpectrumOver P] :
    (over p i P).hom = normalConeπ i P ≫ p := sorry

/-- The structural morphism of a chosen normal-cone model is affine. -/
theorem normalConeπ_isAffine (i : Z ⟶ X) [IsImmersion i]
    (P : RelativeSpectrumOver (ConormalAlgebra.total i)) [IsRelativeSpectrumOver P] :
    IsAffineHom (normalConeπ i P) := sorry

/-- A normal cone of a closed immersion into a locally Noetherian scheme is locally of
finite type over every locally finite-type further base. -/
theorem over_locallyOfFiniteType (p : Z ⟶ S) [LocallyOfFiniteType p]
    (i : Z ⟶ X) [IsClosedImmersion i] [IsLocallyNoetherian X]
    (P : RelativeSpectrumOver (ConormalAlgebra.total i)) [IsRelativeSpectrumOver P] :
    LocallyOfFiniteType (over p i P).hom := sorry

/-- A normal cone locally of finite type over a locally Noetherian base is locally
Noetherian. -/
theorem over_isLocallyNoetherian (p : Z ⟶ S) [IsLocallyNoetherian S]
    (i : Z ⟶ X) [IsClosedImmersion i]
    (P : RelativeSpectrumOver (ConormalAlgebra.total i)) [IsRelativeSpectrumOver P]
    [LocallyOfFiniteType (over p i P).hom] :
    IsLocallyNoetherian (over p i P).left := sorry

/-- The conormal sheaf of an effective Cartier divisor is invertible. -/
theorem conormalSheaf_invertible (j : Y ⟶ X) [IsEffectiveCartierDivisor j] :
    Modules.Invertible (Hom.conormalSheaf j) := sorry

/-- For an effective Cartier divisor, the canonical map from its normal cone to its normal
bundle is an isomorphism. -/
theorem normalConeToNormalBundle_isIso (j : Y ⟶ X) [IsEffectiveCartierDivisor j]
    (PC : RelativeSpectrumOver (ConormalAlgebra.total j)) [IsRelativeSpectrumOver PC]
    (PN : RelativeSpectrumOver (SymmetricAlgebra.qcAlgebra (Hom.conormalSheaf j)))
    [IsRelativeSpectrumOver PN] :
    IsIso (normalConeToNormalBundle j PC PN) := sorry

/-- The commutative square of immersions used for conormal transitivity. -/
theorem transitivitySquare (i : Z ⟶ Y) (j : Y ⟶ X) :
    CommSq (𝟙 Z) i (i ≫ j) j := sorry

/-- The identity-pullback comparison preserves the unit of a graded algebra sheaf. -/
theorem identityPullbackGradedMap_map_one
    (A : GradedAlgebraSheaf.{u, u} Z.sheaf ℕ) (U : (Opens Z)ᵒᵖ) :
    (((((Modules.pullbackId Z).inv.app (A.obj 0)).val.app U).hom) (A.one U)) =
      (Modules.GradedAlgebra.pullback (𝟙 Z) A).one U := sorry

/-- The identity-pullback comparison preserves multiplication in a graded algebra sheaf. -/
theorem identityPullbackGradedMap_map_mul
    (A : GradedAlgebraSheaf.{u, u} Z.sheaf ℕ) (U : (Opens Z)ᵒᵖ) (n m : ℕ)
    (a : (A.obj n).val.obj U) (b : (A.obj m).val.obj U) :
    (((((Modules.pullbackId Z).inv.app (A.obj (n + m))).val.app U).hom)
        (A.mul U n m a b)) =
      (Modules.GradedAlgebra.pullback (𝟙 Z) A).mul U n m
        (((((Modules.pullbackId Z).inv.app (A.obj n)).val.app U).hom) a)
        (((((Modules.pullbackId Z).inv.app (A.obj m)).val.app U).hom) b) := sorry

/-- The graded-algebra comparison from a conormal algebra to its pullback along the identity. -/
noncomputable def identityPullbackGradedMap
    (A : GradedAlgebraSheaf.{u, u} Z.sheaf ℕ) :
    GradedAlgebraSheaf.Hom.{u, u} A (Modules.GradedAlgebra.pullback (𝟙 Z) A) where
  hom n := (Modules.pullbackId Z).inv.app (A.obj n)
  map_one := identityPullbackGradedMap_map_one A
  map_mul := identityPullbackGradedMap_map_mul A

/-- The identity-pullback graded map is degreewise the inverse identity-pullback comparison. -/
theorem identityPullbackGradedMap_hom
    (A : GradedAlgebraSheaf.{u, u} Z.sheaf ℕ) (n : ℕ) :
    (identityPullbackGradedMap A).hom n =
      (Modules.pullbackId Z).inv.app (A.obj n) := sorry

/-- Pullback along the identity followed by the conormal-algebra transitivity map. -/
theorem ambientGradedMap_map_one (i : Z ⟶ Y) (j : Y ⟶ X)
    [IsImmersion i] [IsImmersion (i ≫ j)] (U : (Opens Z)ᵒᵖ) :
    (((((Modules.pullbackId Z).inv.app ((ConormalAlgebra (i ≫ j)).obj 0) ≫
        (ConormalAlgebra.map (transitivitySquare i j)).hom 0).val.app U).hom)
          ((ConormalAlgebra (i ≫ j)).one U)) =
      (ConormalAlgebra i).one U := sorry

/-- The graded transitivity map preserves multiplication. -/
theorem ambientGradedMap_map_mul (i : Z ⟶ Y) (j : Y ⟶ X)
    [IsImmersion i] [IsImmersion (i ≫ j)] (U : (Opens Z)ᵒᵖ) (n m : ℕ)
    (a : ((ConormalAlgebra (i ≫ j)).obj n).val.obj U)
    (b : ((ConormalAlgebra (i ≫ j)).obj m).val.obj U) :
    (((((Modules.pullbackId Z).inv.app ((ConormalAlgebra (i ≫ j)).obj (n + m)) ≫
        (ConormalAlgebra.map (transitivitySquare i j)).hom (n + m)).val.app U).hom)
          ((ConormalAlgebra (i ≫ j)).mul U n m a b)) =
      (ConormalAlgebra i).mul U n m
        (((((Modules.pullbackId Z).inv.app ((ConormalAlgebra (i ≫ j)).obj n) ≫
          (ConormalAlgebra.map (transitivitySquare i j)).hom n).val.app U).hom) a)
        (((((Modules.pullbackId Z).inv.app ((ConormalAlgebra (i ≫ j)).obj m) ≫
          (ConormalAlgebra.map (transitivitySquare i j)).hom m).val.app U).hom) b) := sorry

/-- Pullback along the identity followed by the conormal-algebra transitivity map. -/
noncomputable def ambientGradedMap (i : Z ⟶ Y) (j : Y ⟶ X)
    [IsImmersion i] [IsImmersion (i ≫ j)] :
    GradedAlgebraSheaf.Hom.{u, u} (ConormalAlgebra (i ≫ j)) (ConormalAlgebra i) :=
  { hom := fun n ↦ (Modules.pullbackId Z).inv.app ((ConormalAlgebra (i ≫ j)).obj n) ≫
      (ConormalAlgebra.map (transitivitySquare i j)).hom n
    map_one := ambientGradedMap_map_one i j
    map_mul := ambientGradedMap_map_mul i j }

/-- The canonical map from the total conormal algebra of `Z` in `X` to that of `Z` in `Y`. -/
noncomputable def ambientAlgebraMap (i : Z ⟶ Y) (j : Y ⟶ X)
    [IsImmersion i] [IsImmersion (i ≫ j)] :
    ConormalAlgebra.total (i ≫ j) ⟶ ConormalAlgebra.total i :=
  ⟨@GradedAlgebraSheaf.totalMap.{u, u, u} _ _ _ _ _ _ _ Z.sheaf
      (ConormalAlgebra (i ≫ j)) (ConormalAlgebra i)
      (KernelIdeal.AssociatedGraded.algebra_isCommutative.{u, u}
        (RingedSpace.Hom.inverseImageStructureSheafHomComm (i ≫ j).toShHom))
      (KernelIdeal.AssociatedGraded.algebra_isCommutative.{u, u}
        (RingedSpace.Hom.inverseImageStructureSheafHomComm i.toShHom))
      (ambientGradedMap i j)⟩

/-- The underlying algebra-sheaf map of `ambientAlgebraMap` is induced by totalizing the
canonical graded conormal-algebra comparison. -/
theorem ambientAlgebraMap_obj (i : Z ⟶ Y) (j : Y ⟶ X)
    [IsImmersion i] [IsImmersion (i ≫ j)] :
    (QcAlgebraUnder.forget Z).map (ambientAlgebraMap i j) =
      @GradedAlgebraSheaf.totalMap.{u, u, u} _ _ _ _ _ _ _ Z.sheaf
      (ConormalAlgebra (i ≫ j)) (ConormalAlgebra i)
      (KernelIdeal.AssociatedGraded.algebra_isCommutative.{u, u}
        (RingedSpace.Hom.inverseImageStructureSheafHomComm (i ≫ j).toShHom))
      (KernelIdeal.AssociatedGraded.algebra_isCommutative.{u, u}
        (RingedSpace.Hom.inverseImageStructureSheafHomComm i.toShHom))
      (ambientGradedMap i j) := sorry

/-- The canonical morphism from `C_Z Y` to `C_Z X`. -/
noncomputable def toAmbient (i : Z ⟶ Y) (j : Y ⟶ X)
    [IsImmersion i] [IsImmersion (i ≫ j)]
    (PZY : RelativeSpectrumOver (ConormalAlgebra.total i)) [IsRelativeSpectrumOver PZY]
    (PZX : RelativeSpectrumOver (ConormalAlgebra.total (i ≫ j)))
    [IsRelativeSpectrumOver PZX] :
    normalCone i PZY ⟶ normalCone (i ≫ j) PZX :=
  (IsRelativeSpectrumOver.isRepresentedBy (P := PZX)).representableBy.homEquiv.symm
    (⟨normalConeπ i PZY,
      (QcAlgebraUnder.forget Z).map (ambientAlgebraMap i j) ≫
        relativeSpecUniversalFamily PZY⟩ :
      relativeSpectrumPair (ConormalAlgebra.total (i ≫ j)) (normalCone i PZY))

/-- Pulling back the universal point of `C_Z X` along `toAmbient` gives the point induced by
the canonical total conormal-algebra comparison. -/
theorem toAmbient_spec (i : Z ⟶ Y) (j : Y ⟶ X)
    [IsImmersion i] [IsImmersion (i ≫ j)]
    (PZY : RelativeSpectrumOver (ConormalAlgebra.total i)) [IsRelativeSpectrumOver PZY]
    (PZX : RelativeSpectrumOver (ConormalAlgebra.total (i ≫ j)))
    [IsRelativeSpectrumOver PZX] :
    relativeSpectrumPairPullbackMap (ConormalAlgebra.total (i ≫ j))
        (toAmbient i j PZY PZX) (relativeSpecPoint PZX) =
      (⟨normalConeπ i PZY,
        (QcAlgebraUnder.forget Z).map (ambientAlgebraMap i j) ≫
          relativeSpecUniversalFamily PZY⟩ :
        relativeSpectrumPair (ConormalAlgebra.total (i ≫ j)) (normalCone i PZY)) := sorry

/-- The canonical morphism `C_Z Y ⟶ C_Z X` lies over `Z`. -/
theorem toAmbient_π (i : Z ⟶ Y) (j : Y ⟶ X)
    [IsImmersion i] [IsImmersion (i ≫ j)]
    (PZY : RelativeSpectrumOver (ConormalAlgebra.total i)) [IsRelativeSpectrumOver PZY]
    (PZX : RelativeSpectrumOver (ConormalAlgebra.total (i ≫ j)))
    [IsRelativeSpectrumOver PZX] :
    toAmbient i j PZY PZX ≫ normalConeπ (i ≫ j) PZX = normalConeπ i PZY := sorry

/-- The universal algebra morphism carried by a chosen normal-cone model. -/
noncomputable def universalAlgebraMap (i : Z ⟶ X) [IsImmersion i]
    (P : RelativeSpectrumOver (ConormalAlgebra.total i)) [IsRelativeSpectrumOver P] :
    -- Local instance justification (proof-local temporary data): supplies affineness needed to infer quasi-compactness and quasi-separatedness for the pushed-forward structure algebra.
    letI : IsAffineHom (normalConeπ i P) := normalConeπ_isAffine i P
    ConormalAlgebra.total i ⟶
      pushforwardStructureSheafQcAlgebra (normalConeπ i P) :=
  -- Local instance justification (proof-local temporary data): supplies affineness needed to infer quasi-compactness and quasi-separatedness for the pushed-forward structure algebra.
  letI : IsAffineHom (normalConeπ i P) := normalConeπ_isAffine i P
  ⟨relativeSpecUniversalFamily P⟩

/-- Forgetting quasi-coherence from `universalAlgebraMap` gives the universal algebra map of
the relative-spectrum model. -/
theorem universalAlgebraMap_obj (i : Z ⟶ X) [IsImmersion i]
    (P : RelativeSpectrumOver (ConormalAlgebra.total i)) [IsRelativeSpectrumOver P] :
    -- Local instance justification (proof-local temporary data): supplies affineness needed to infer quasi-compactness and quasi-separatedness for the pushed-forward structure algebra.
    letI : IsAffineHom (normalConeπ i P) := normalConeπ_isAffine i P
    (QcAlgebraUnder.forget Z).map (universalAlgebraMap i P) =
      relativeSpecUniversalFamily P := sorry

/-- The composite from a normal cone to the source of the outer immersion is affine. -/
theorem toNormalBundleBase_isAffine (i : Z ⟶ Y) [IsClosedImmersion i]
    (j : Y ⟶ X) [IsImmersion (i ≫ j)]
    (PZX : RelativeSpectrumOver (ConormalAlgebra.total (i ≫ j)))
    [IsRelativeSpectrumOver PZX] :
    IsAffineHom (normalConeπ (i ≫ j) PZX ≫ i) := sorry

/-- The module map whose symmetric-algebra extension defines the canonical morphism
`C_Z X ⟶ N_Y X`. -/
noncomputable def toNormalBundleLinear (i : Z ⟶ Y) (j : Y ⟶ X)
    [IsClosedImmersion i] [IsImmersion j] [IsImmersion (i ≫ j)]
    (PZX : RelativeSpectrumOver (ConormalAlgebra.total (i ≫ j)))
    [IsRelativeSpectrumOver PZX] :
    -- Local instance justification (proof-local temporary data): supplies affineness needed to infer quasi-compactness and quasi-separatedness for the composite pushed-forward structure algebra.
    letI : IsAffineHom (normalConeπ (i ≫ j) PZX ≫ i) :=
      toNormalBundleBase_isAffine i j PZX
    -- Local instance justification (proof-local temporary data): supplies affineness needed to infer quasi-compactness and quasi-separatedness for the normal-cone pushed-forward structure algebra.
    letI : IsAffineHom (normalConeπ (i ≫ j) PZX) := normalConeπ_isAffine (i ≫ j) PZX
    Hom.conormalSheaf j ⟶
      QcAlgebraUnder.underlyingModule Y
        (pushforwardStructureSheafQcAlgebra (normalConeπ (i ≫ j) PZX ≫ i)) :=
  -- Local instance justification (proof-local temporary data): supplies affineness needed to infer quasi-compactness and quasi-separatedness for the composite pushed-forward structure algebra.
  letI : IsAffineHom (normalConeπ (i ≫ j) PZX ≫ i) :=
    toNormalBundleBase_isAffine i j PZX
  -- Local instance justification (proof-local temporary data): supplies affineness needed to infer quasi-compactness and quasi-separatedness for the normal-cone pushed-forward structure algebra.
  letI : IsAffineHom (normalConeπ (i ≫ j) PZX) := normalConeπ_isAffine (i ≫ j) PZX
  ((Modules.pullbackPushforwardAdjunction (normalConeπ (i ≫ j) PZX ≫ i)).homEquiv _ _
      ((Modules.pullbackComp (normalConeπ (i ≫ j) PZX) i).inv.app
            (Hom.conormalSheaf j) ≫
        (Modules.pullback (normalConeπ (i ≫ j) PZX)).map
          (Hom.Conormal.Transitivity.baseChange i j) ≫
        (Modules.pullback (normalConeπ (i ≫ j) PZX)).map
          (ConormalAlgebra.degreeOneToTotal (i ≫ j)) ≫
        (Modules.pullback (normalConeπ (i ≫ j) PZX)).map
          (QcAlgebraUnder.underlyingModuleMap Z (universalAlgebraMap (i ≫ j) PZX)) ≫
        (Modules.pullback (normalConeπ (i ≫ j) PZX)).map
          (pushforwardStructureModuleIso (normalConeπ (i ≫ j) PZX)).hom ≫
        (Modules.pullbackPushforwardAdjunction
          (normalConeπ (i ≫ j) PZX)).counit.app
            (unitModule (Opens.grothendieckTopology (normalCone (i ≫ j) PZX))
              (normalCone (i ≫ j) PZX).sheaf))) ≫
    (pushforwardStructureModuleIso (normalConeπ (i ≫ j) PZX ≫ i)).inv

/-- Under pullback to `C_Z X`, `toNormalBundleLinear` is the conormal transitivity map,
followed by the degree-one inclusion and the universal relative-spectrum map. -/
theorem toNormalBundleLinear_adjunct (i : Z ⟶ Y) (j : Y ⟶ X)
    [IsClosedImmersion i] [IsImmersion j] [IsImmersion (i ≫ j)]
    (PZX : RelativeSpectrumOver (ConormalAlgebra.total (i ≫ j)))
    [IsRelativeSpectrumOver PZX] :
    -- Local instance justification (proof-local temporary data): supplies affineness needed to infer quasi-compactness and quasi-separatedness for the composite pushed-forward structure algebra.
    letI : IsAffineHom (normalConeπ (i ≫ j) PZX ≫ i) :=
      toNormalBundleBase_isAffine i j PZX
    -- Local instance justification (proof-local temporary data): supplies affineness needed to infer quasi-compactness and quasi-separatedness for the normal-cone pushed-forward structure algebra.
    letI : IsAffineHom (normalConeπ (i ≫ j) PZX) := normalConeπ_isAffine (i ≫ j) PZX
    toNormalBundleLinear i j PZX ≫
        (pushforwardStructureModuleIso (normalConeπ (i ≫ j) PZX ≫ i)).hom =
      (Modules.pullbackPushforwardAdjunction
          (normalConeπ (i ≫ j) PZX ≫ i)).homEquiv _ _
        ((Modules.pullbackComp (normalConeπ (i ≫ j) PZX) i).inv.app
              (Hom.conormalSheaf j) ≫
          (Modules.pullback (normalConeπ (i ≫ j) PZX)).map
            (Hom.Conormal.Transitivity.baseChange i j) ≫
          (Modules.pullback (normalConeπ (i ≫ j) PZX)).map
            (ConormalAlgebra.degreeOneToTotal (i ≫ j)) ≫
          (Modules.pullback (normalConeπ (i ≫ j) PZX)).map
            (QcAlgebraUnder.underlyingModuleMap Z (universalAlgebraMap (i ≫ j) PZX)) ≫
          (Modules.pullback (normalConeπ (i ≫ j) PZX)).map
            (pushforwardStructureModuleIso (normalConeπ (i ≫ j) PZX)).hom ≫
          (Modules.pullbackPushforwardAdjunction
            (normalConeπ (i ≫ j) PZX)).counit.app
              (unitModule (Opens.grothendieckTopology (normalCone (i ≫ j) PZX))
                (normalCone (i ≫ j) PZX).sheaf)) := sorry

/-- The symmetric-algebra morphism induced by conormal transitivity for nested immersions. -/
noncomputable def toNormalBundleAlgebraMap (i : Z ⟶ Y) (j : Y ⟶ X)
    [IsClosedImmersion i] [IsImmersion j] [IsImmersion (i ≫ j)]
    (PZX : RelativeSpectrumOver (ConormalAlgebra.total (i ≫ j)))
    [IsRelativeSpectrumOver PZX] :
    -- Local instance justification (proof-local temporary data): supplies affineness needed to infer quasi-compactness and quasi-separatedness for the composite pushed-forward structure algebra.
    letI : IsAffineHom (normalConeπ (i ≫ j) PZX ≫ i) :=
      toNormalBundleBase_isAffine i j PZX
    SymmetricAlgebra.qcAlgebra (Hom.conormalSheaf j) ⟶
      pushforwardStructureSheafQcAlgebra (normalConeπ (i ≫ j) PZX ≫ i) :=
  -- Local instance justification (proof-local temporary data): supplies affineness needed to infer quasi-compactness and quasi-separatedness for the composite pushed-forward structure algebra.
  letI : IsAffineHom (normalConeπ (i ≫ j) PZX ≫ i) :=
    toNormalBundleBase_isAffine i j PZX
  SymmetricAlgebra.lift (Hom.conormalSheaf j)
    (pushforwardStructureSheafQcAlgebra (normalConeπ (i ≫ j) PZX ≫ i))
    (toNormalBundleLinear i j PZX)

/-- The conormal generators of `toNormalBundleAlgebraMap` are sent by
`toNormalBundleLinear`. -/
theorem toNormalBundleAlgebraMap_ι (i : Z ⟶ Y) (j : Y ⟶ X)
    [IsClosedImmersion i] [IsImmersion j] [IsImmersion (i ≫ j)]
    (PZX : RelativeSpectrumOver (ConormalAlgebra.total (i ≫ j)))
    [IsRelativeSpectrumOver PZX] :
    -- Local instance justification (proof-local temporary data): supplies affineness needed to infer quasi-compactness and quasi-separatedness for the composite pushed-forward structure algebra.
    letI : IsAffineHom (normalConeπ (i ≫ j) PZX ≫ i) :=
      toNormalBundleBase_isAffine i j PZX
    SymmetricAlgebra.ι (Hom.conormalSheaf j) ≫
        QcAlgebraUnder.underlyingModuleMap Y (toNormalBundleAlgebraMap i j PZX) =
      toNormalBundleLinear i j PZX := sorry

/-- The canonical morphism from `C_Z X` to the normal bundle `N_Y X`. -/
noncomputable def toNormalBundle (i : Z ⟶ Y) (j : Y ⟶ X)
    [IsClosedImmersion i] [IsImmersion j] [IsImmersion (i ≫ j)]
    (PZX : RelativeSpectrumOver (ConormalAlgebra.total (i ≫ j)))
    [IsRelativeSpectrumOver PZX]
    (PNY : RelativeSpectrumOver (SymmetricAlgebra.qcAlgebra (Hom.conormalSheaf j)))
    [IsRelativeSpectrumOver PNY] :
    normalCone (i ≫ j) PZX ⟶ normalBundle j PNY :=
  (IsRelativeSpectrumOver.isRepresentedBy (P := PNY)).representableBy.homEquiv.symm
    (⟨normalConeπ (i ≫ j) PZX ≫ i,
      (QcAlgebraUnder.forget Y).map (toNormalBundleAlgebraMap i j PZX)⟩ :
      relativeSpectrumPair (SymmetricAlgebra.qcAlgebra (Hom.conormalSheaf j))
        (normalCone (i ≫ j) PZX))

/-- Pulling back the universal point of `N_Y X` along `toNormalBundle` gives the point induced
by conormal transitivity. -/
theorem toNormalBundle_spec (i : Z ⟶ Y) (j : Y ⟶ X)
    [IsClosedImmersion i] [IsImmersion j] [IsImmersion (i ≫ j)]
    (PZX : RelativeSpectrumOver (ConormalAlgebra.total (i ≫ j)))
    [IsRelativeSpectrumOver PZX]
    (PNY : RelativeSpectrumOver (SymmetricAlgebra.qcAlgebra (Hom.conormalSheaf j)))
    [IsRelativeSpectrumOver PNY] :
    relativeSpectrumPairPullbackMap (SymmetricAlgebra.qcAlgebra (Hom.conormalSheaf j))
        (toNormalBundle i j PZX PNY) (relativeSpecPoint PNY) =
      (⟨normalConeπ (i ≫ j) PZX ≫ i,
        (QcAlgebraUnder.forget Y).map (toNormalBundleAlgebraMap i j PZX)⟩ :
        relativeSpectrumPair (SymmetricAlgebra.qcAlgebra (Hom.conormalSheaf j))
          (normalCone (i ≫ j) PZX)) := sorry

/-- The canonical morphism `C_Z X ⟶ N_Y X` lies over `Y`. -/
theorem toNormalBundle_π (i : Z ⟶ Y) (j : Y ⟶ X)
    [IsClosedImmersion i] [IsImmersion j] [IsImmersion (i ≫ j)]
    (PZX : RelativeSpectrumOver (ConormalAlgebra.total (i ≫ j)))
    [IsRelativeSpectrumOver PZX]
    (PNY : RelativeSpectrumOver (SymmetricAlgebra.qcAlgebra (Hom.conormalSheaf j)))
    [IsRelativeSpectrumOver PNY] :
    toNormalBundle i j PZX PNY ≫ normalBundleπ j PNY =
      normalConeπ (i ≫ j) PZX ≫ i := sorry

/-- For nested effective Cartier divisors, the canonical map from the ambient normal cone to
the outer normal line bundle is locally of finite type. -/
theorem toNormalBundle_locallyOfFiniteType (i : Z ⟶ Y) (j : Y ⟶ X)
    [IsClosedImmersion i] [IsEffectiveCartierDivisor j]
    [IsEffectiveCartierDivisor (i ≫ j)]
    (PZX : RelativeSpectrumOver (ConormalAlgebra.total (i ≫ j)))
    [IsRelativeSpectrumOver PZX]
    (PNY : RelativeSpectrumOver (SymmetricAlgebra.qcAlgebra (Hom.conormalSheaf j)))
    [IsRelativeSpectrumOver PNY] :
    LocallyOfFiniteType (toNormalBundle i j PZX PNY) := sorry

/-- The canonical map from `C_Z Y` to `C_Z X` commutes with their structure maps to a
further base scheme. -/
theorem toAmbient_structure (p : X ⟶ S) (i : Z ⟶ Y) (j : Y ⟶ X)
    [IsImmersion i] [IsImmersion (i ≫ j)]
    (PZY : RelativeSpectrumOver (ConormalAlgebra.total i)) [IsRelativeSpectrumOver PZY]
    (PZX : RelativeSpectrumOver (ConormalAlgebra.total (i ≫ j)))
    [IsRelativeSpectrumOver PZX] :
    toAmbient i j PZY PZX ≫ (over (i ≫ j ≫ p) (i ≫ j) PZX).hom =
      (over (i ≫ j ≫ p) i PZY).hom := sorry

/-- The canonical morphism `C_Z Y ⟶ C_Z X`, regarded over a further base scheme. -/
noncomputable def toAmbientOver (p : X ⟶ S) (i : Z ⟶ Y) (j : Y ⟶ X)
    [IsImmersion i] [IsImmersion (i ≫ j)]
    (PZY : RelativeSpectrumOver (ConormalAlgebra.total i)) [IsRelativeSpectrumOver PZY]
    (PZX : RelativeSpectrumOver (ConormalAlgebra.total (i ≫ j)))
    [IsRelativeSpectrumOver PZX] :
    over (i ≫ j ≫ p) i PZY ⟶ over (i ≫ j ≫ p) (i ≫ j) PZX :=
  Over.homMk (toAmbient i j PZY PZX) (toAmbient_structure p i j PZY PZX)

/-- The underlying scheme morphism of `toAmbientOver` is the canonical ambient normal-cone
map. -/
theorem toAmbientOver_left (p : X ⟶ S) (i : Z ⟶ Y) (j : Y ⟶ X)
    [IsImmersion i] [IsImmersion (i ≫ j)]
    (PZY : RelativeSpectrumOver (ConormalAlgebra.total i)) [IsRelativeSpectrumOver PZY]
    (PZX : RelativeSpectrumOver (ConormalAlgebra.total (i ≫ j)))
    [IsRelativeSpectrumOver PZX] :
    (toAmbientOver p i j PZY PZX).left = toAmbient i j PZY PZX := sorry

/-- The canonical map `C_Z X ⟶ N_Y X` commutes with the structure maps to a further
base scheme. -/
theorem toNormalBundle_structure (p : X ⟶ S) (i : Z ⟶ Y) (j : Y ⟶ X)
    [IsClosedImmersion i] [IsEffectiveCartierDivisor j] [IsImmersion (i ≫ j)]
    [hL : Modules.Invertible (Hom.conormalSheaf j)]
    (PZX : RelativeSpectrumOver (ConormalAlgebra.total (i ≫ j)))
    [IsRelativeSpectrumOver PZX]
    (PNY : RelativeSpectrumOver (SymmetricAlgebra.qcAlgebra (Hom.conormalSheaf j)))
    [hPNY : IsRelativeSpectrumOver PNY] :
    toNormalBundle i j PZX PNY ≫
        (@AssociatedVectorBundle.totalOver _ (Over.mk (j ≫ p)) (Hom.conormalSheaf j)
          hL PNY hPNY).hom =
      (over (i ≫ j ≫ p) (i ≫ j) PZX).hom := sorry

/-- The canonical morphism `C_Z X ⟶ N_Y X`, regarded over a further base scheme. -/
noncomputable def toNormalBundleOver (p : X ⟶ S) (i : Z ⟶ Y) (j : Y ⟶ X)
    [IsClosedImmersion i] [IsEffectiveCartierDivisor j] [IsImmersion (i ≫ j)]
    [hL : Modules.Invertible (Hom.conormalSheaf j)]
    (PZX : RelativeSpectrumOver (ConormalAlgebra.total (i ≫ j)))
    [IsRelativeSpectrumOver PZX]
    (PNY : RelativeSpectrumOver (SymmetricAlgebra.qcAlgebra (Hom.conormalSheaf j)))
    [hPNY : IsRelativeSpectrumOver PNY] :
    over (i ≫ j ≫ p) (i ≫ j) PZX ⟶
      @AssociatedVectorBundle.totalOver _ (Over.mk (j ≫ p)) (Hom.conormalSheaf j)
        hL PNY hPNY :=
  Over.homMk (toNormalBundle i j PZX PNY) (toNormalBundle_structure p i j PZX PNY)

/-- The canonical normal-cone morphism to the outer normal bundle is locally of finite
type on underlying schemes. -/
theorem toNormalBundleOver_locallyOfFiniteType (p : X ⟶ S)
    (i : Z ⟶ Y) (j : Y ⟶ X) [IsClosedImmersion i]
    [IsEffectiveCartierDivisor j] [IsEffectiveCartierDivisor (i ≫ j)]
    [hL : Modules.Invertible (Hom.conormalSheaf j)]
    (PZX : RelativeSpectrumOver (ConormalAlgebra.total (i ≫ j)))
    [IsRelativeSpectrumOver PZX]
    (PNY : RelativeSpectrumOver (SymmetricAlgebra.qcAlgebra (Hom.conormalSheaf j)))
    [hPNY : IsRelativeSpectrumOver PNY] :
    LocallyOfFiniteType (toNormalBundleOver p i j PZX PNY).left := sorry

/-- The underlying scheme morphism of `toNormalBundleOver` is the canonical map to the
normal bundle. -/
theorem toNormalBundleOver_left (p : X ⟶ S) (i : Z ⟶ Y) (j : Y ⟶ X)
    [IsClosedImmersion i] [IsEffectiveCartierDivisor j] [IsImmersion (i ≫ j)]
    [hL : Modules.Invertible (Hom.conormalSheaf j)]
    (PZX : RelativeSpectrumOver (ConormalAlgebra.total (i ≫ j)))
    [IsRelativeSpectrumOver PZX]
    (PNY : RelativeSpectrumOver (SymmetricAlgebra.qcAlgebra (Hom.conormalSheaf j)))
    [hPNY : IsRelativeSpectrumOver PNY] :
    (toNormalBundleOver p i j PZX PNY).left = toNormalBundle i j PZX PNY := sorry

/-- The canonical map to the chosen zero-scheme presentation of the zero section. -/
noncomputable def toZeroSchemeOver (p : X ⟶ S) (i : Z ⟶ Y) (j : Y ⟶ X)
    [IsImmersion i] [IsEffectiveCartierDivisor j]
    [hL : Modules.Invertible (Hom.conormalSheaf j)]
    (PZY : RelativeSpectrumOver (ConormalAlgebra.total i)) [IsRelativeSpectrumOver PZY]
    (PNY : RelativeSpectrumOver (SymmetricAlgebra.qcAlgebra (Hom.conormalSheaf j)))
    [hPNY : IsRelativeSpectrumOver PNY]
    (sigma : (@AssociatedVectorBundle.inverseLine _ (Over.mk (j ≫ p))
      (Hom.conormalSheaf j) hL PNY hPNY).sections)
    (e : Over.mk (j ≫ p) ≅ @AssociatedVectorBundle.zeroSchemeOver _
      (Over.mk (j ≫ p)) (Hom.conormalSheaf j) hL PNY hPNY sigma) :
    over (i ≫ j ≫ p) i PZY ⟶ @AssociatedVectorBundle.zeroSchemeOver _
      (Over.mk (j ≫ p)) (Hom.conormalSheaf j) hL PNY hPNY sigma :=
  (Over.homMk (normalConeπ i PZY) : over (i ≫ j ≫ p) i PZY ⟶
      Over.mk (i ≫ j ≫ p)) ≫
    (Over.homMk i : Over.mk (i ≫ j ≫ p) ⟶ Over.mk (j ≫ p)) ≫ e.hom

/-- The map `toZeroSchemeOver` is the normal-cone projection followed by the nested
immersion and the chosen zero-scheme identification. -/
theorem toZeroSchemeOver_left (p : X ⟶ S) (i : Z ⟶ Y) (j : Y ⟶ X)
    [IsImmersion i] [IsEffectiveCartierDivisor j]
    [hL : Modules.Invertible (Hom.conormalSheaf j)]
    (PZY : RelativeSpectrumOver (ConormalAlgebra.total i)) [IsRelativeSpectrumOver PZY]
    (PNY : RelativeSpectrumOver (SymmetricAlgebra.qcAlgebra (Hom.conormalSheaf j)))
    [hPNY : IsRelativeSpectrumOver PNY]
    (sigma : (@AssociatedVectorBundle.inverseLine _ (Over.mk (j ≫ p))
      (Hom.conormalSheaf j) hL PNY hPNY).sections)
    (e : Over.mk (j ≫ p) ≅ @AssociatedVectorBundle.zeroSchemeOver _
      (Over.mk (j ≫ p)) (Hom.conormalSheaf j) hL PNY hPNY sigma) :
    (toZeroSchemeOver p i j PZY PNY sigma e).left =
      normalConeπ i PZY ≫ i ≫ e.hom.left := sorry

/-- The relative normal-cone comparison commutes with the zero-section immersion and
the ambient normal-cone map. -/
theorem zeroSectionSquare_comm (p : X ⟶ S) (i : Z ⟶ Y) (j : Y ⟶ X)
    [IsClosedImmersion i] [IsEffectiveCartierDivisor j]
    [IsEffectiveCartierDivisor (i ≫ j)]
    [hL : Modules.Invertible (Hom.conormalSheaf j)]
    (PZY : RelativeSpectrumOver (ConormalAlgebra.total i)) [IsRelativeSpectrumOver PZY]
    (PZX : RelativeSpectrumOver (ConormalAlgebra.total (i ≫ j)))
    [IsRelativeSpectrumOver PZX]
    (PNY : RelativeSpectrumOver (SymmetricAlgebra.qcAlgebra (Hom.conormalSheaf j)))
    [hPNY : IsRelativeSpectrumOver PNY]
    (sigma : (@AssociatedVectorBundle.inverseLine _ (Over.mk (j ≫ p))
      (Hom.conormalSheaf j) hL PNY hPNY).sections)
    (e : Over.mk (j ≫ p) ≅ @AssociatedVectorBundle.zeroSchemeOver _
      (Over.mk (j ≫ p)) (Hom.conormalSheaf j) hL PNY hPNY sigma)
    (h_e : e.hom.left ≫
      @Scheme.zeroSchemeι
        (@AssociatedVectorBundle.totalOver _ (Over.mk (j ≫ p))
          (Hom.conormalSheaf j) hL PNY hPNY).left _
        (@AssociatedVectorBundle.inverseLine _ (Over.mk (j ≫ p))
          (Hom.conormalSheaf j) hL PNY hPNY)
        (Modules.Invertible.tensorRight_isEquivalence
          (@AssociatedVectorBundle.inverseLine_invertible _
            (Over.mk (j ≫ p)) (Hom.conormalSheaf j) hL PNY hPNY)) sigma =
      @AssociatedVectorBundle.zeroSection _ (Over.mk (j ≫ p))
        (Hom.conormalSheaf j) hL PNY hPNY) :
    (toZeroSchemeOver p i j PZY PNY sigma e).left ≫
      (@Scheme.zeroSchemeι
        (@AssociatedVectorBundle.totalOver _ (Over.mk (j ≫ p))
          (Hom.conormalSheaf j) hL PNY hPNY).left _
        (@AssociatedVectorBundle.inverseLine _ (Over.mk (j ≫ p))
          (Hom.conormalSheaf j) hL PNY hPNY)
        (Modules.Invertible.tensorRight_isEquivalence
          (@AssociatedVectorBundle.inverseLine_invertible _
            (Over.mk (j ≫ p)) (Hom.conormalSheaf j) hL PNY hPNY)) sigma) =
    (toAmbientOver p i j PZY PZX).left ≫
      (toNormalBundleOver p i j PZX PNY).left := sorry

section ZeroSectionFiber

variable (p : X ⟶ S) (i : Z ⟶ Y) (j : Y ⟶ X)
variable [IsClosedImmersion i] [IsEffectiveCartierDivisor j]
variable [IsEffectiveCartierDivisor (i ≫ j)]
variable [hL : Modules.Invertible (Hom.conormalSheaf j)]
variable (PZY : RelativeSpectrumOver (ConormalAlgebra.total i)) [IsRelativeSpectrumOver PZY]
variable (PZX : RelativeSpectrumOver (ConormalAlgebra.total (i ≫ j)))
variable [IsRelativeSpectrumOver PZX]
variable (PNY : RelativeSpectrumOver (SymmetricAlgebra.qcAlgebra (Hom.conormalSheaf j)))
variable [hPNY : IsRelativeSpectrumOver PNY]
variable (sigma : (@AssociatedVectorBundle.inverseLine _ (Over.mk (j ≫ p))
  (Hom.conormalSheaf j) hL PNY hPNY).sections)

/-- The fiber of the ambient normal-cone map over the zero scheme of the outer normal
line bundle, regarded over the original base through the ambient cone. -/
noncomputable def zeroSectionFiber : Over S :=
  Over.mk (pullback.snd (@Scheme.zeroSchemeι
        (@AssociatedVectorBundle.totalOver _ (Over.mk (j ≫ p))
          (Hom.conormalSheaf j) hL PNY hPNY).left _
        (@AssociatedVectorBundle.inverseLine _ (Over.mk (j ≫ p))
          (Hom.conormalSheaf j) hL PNY hPNY)
        (Modules.Invertible.tensorRight_isEquivalence
          (@AssociatedVectorBundle.inverseLine_invertible _
            (Over.mk (j ≫ p)) (Hom.conormalSheaf j) hL PNY hPNY)) sigma) (toNormalBundleOver p i j PZX PNY).left ≫
    (over (i ≫ j ≫ p) (i ≫ j) PZX).hom)

/-- The projection of the zero-section fiber to the chosen zero-scheme presentation. -/
noncomputable def zeroSectionFiberFst :
    zeroSectionFiber p i j PZX PNY sigma ⟶
      @AssociatedVectorBundle.zeroSchemeOver _ (Over.mk (j ≫ p))
        (Hom.conormalSheaf j) hL PNY hPNY sigma :=
  Over.homMk (pullback.fst (@Scheme.zeroSchemeι
        (@AssociatedVectorBundle.totalOver _ (Over.mk (j ≫ p))
          (Hom.conormalSheaf j) hL PNY hPNY).left _
        (@AssociatedVectorBundle.inverseLine _ (Over.mk (j ≫ p))
          (Hom.conormalSheaf j) hL PNY hPNY)
        (Modules.Invertible.tensorRight_isEquivalence
          (@AssociatedVectorBundle.inverseLine_invertible _
            (Over.mk (j ≫ p)) (Hom.conormalSheaf j) hL PNY hPNY)) sigma) (toNormalBundleOver p i j PZX PNY).left) (by
    change _ ≫ ((@Scheme.zeroSchemeι
        (@AssociatedVectorBundle.totalOver _ (Over.mk (j ≫ p))
          (Hom.conormalSheaf j) hL PNY hPNY).left _
        (@AssociatedVectorBundle.inverseLine _ (Over.mk (j ≫ p))
          (Hom.conormalSheaf j) hL PNY hPNY)
        (Modules.Invertible.tensorRight_isEquivalence
          (@AssociatedVectorBundle.inverseLine_invertible _
            (Over.mk (j ≫ p)) (Hom.conormalSheaf j) hL PNY hPNY)) sigma) ≫ _) = _ ≫ _
    exact (Category.assoc _ _ _).symm.trans
      ((congrArg (fun k => k ≫
          (@AssociatedVectorBundle.totalOver _ (Over.mk (j ≫ p))
            (Hom.conormalSheaf j) hL PNY hPNY).hom)
        (pullback.condition)).trans
        ((Category.assoc _ _ _).trans
          (congrArg (fun k => pullback.snd _ _ ≫ k)
            (toNormalBundleOver p i j PZX PNY).w))))

/-- The projection of the zero-section fiber to the ambient normal cone. -/
noncomputable def zeroSectionFiberSnd :
    zeroSectionFiber p i j PZX PNY sigma ⟶ over (i ≫ j ≫ p) (i ≫ j) PZX :=
  Over.homMk (pullback.snd (@Scheme.zeroSchemeι
        (@AssociatedVectorBundle.totalOver _ (Over.mk (j ≫ p))
          (Hom.conormalSheaf j) hL PNY hPNY).left _
        (@AssociatedVectorBundle.inverseLine _ (Over.mk (j ≫ p))
          (Hom.conormalSheaf j) hL PNY hPNY)
        (Modules.Invertible.tensorRight_isEquivalence
          (@AssociatedVectorBundle.inverseLine_invertible _
            (Over.mk (j ≫ p)) (Hom.conormalSheaf j) hL PNY hPNY)) sigma) (toNormalBundleOver p i j PZX PNY).left)

/-- The zero-section fiber is locally of finite type over the base whenever the ambient
normal cone is locally of finite type over that base. -/
theorem zeroSectionFiber_locallyOfFiniteType
    [LocallyOfFiniteType (over (i ≫ j ≫ p) (i ≫ j) PZX).hom] :
    LocallyOfFiniteType (zeroSectionFiber p i j PZX PNY sigma).hom := sorry

variable (e : Over.mk (j ≫ p) ≅ @AssociatedVectorBundle.zeroSchemeOver _
  (Over.mk (j ≫ p)) (Hom.conormalSheaf j) hL PNY hPNY sigma)
variable (h_e : e.hom.left ≫
      @Scheme.zeroSchemeι
        (@AssociatedVectorBundle.totalOver _ (Over.mk (j ≫ p))
          (Hom.conormalSheaf j) hL PNY hPNY).left _
        (@AssociatedVectorBundle.inverseLine _ (Over.mk (j ≫ p))
          (Hom.conormalSheaf j) hL PNY hPNY)
        (Modules.Invertible.tensorRight_isEquivalence
          (@AssociatedVectorBundle.inverseLine_invertible _
            (Over.mk (j ≫ p)) (Hom.conormalSheaf j) hL PNY hPNY)) sigma =
      @AssociatedVectorBundle.zeroSection _ (Over.mk (j ≫ p))
        (Hom.conormalSheaf j) hL PNY hPNY)

/-- The canonical morphism from the relative normal cone into the zero-section fiber. -/
noncomputable def toZeroSectionFiber :
    over (i ≫ j ≫ p) i PZY ⟶ zeroSectionFiber p i j PZX PNY sigma :=
  Over.homMk
    (pullback.lift (toZeroSchemeOver p i j PZY PNY sigma e).left
      (toAmbientOver p i j PZY PZX).left
      (zeroSectionSquare_comm p i j PZY PZX PNY sigma e h_e)) (by
        change _ ≫ (pullback.snd _ _ ≫ _) = _
        exact (Category.assoc _ _ _).symm.trans
          ((congrArg (fun k => k ≫ (over (i ≫ j ≫ p) (i ≫ j) PZX).hom)
            (pullback.lift_snd _ _ _)).trans
            (toAmbientOver p i j PZY PZX).w))

/-- The relative-cone comparison followed by the first fiber projection is the map to the
zero-scheme presentation. -/
theorem toZeroSectionFiber_fst :
    toZeroSectionFiber p i j PZY PZX PNY sigma e h_e ≫
      zeroSectionFiberFst p i j PZX PNY sigma = toZeroSchemeOver p i j PZY PNY sigma e := by
  apply Over.OverMorphism.ext
  exact pullback.lift_fst _ _ _

/-- The relative-cone comparison followed by the second fiber projection is the ambient
normal-cone comparison. -/
theorem toZeroSectionFiber_snd :
    toZeroSectionFiber p i j PZY PZX PNY sigma e h_e ≫
      zeroSectionFiberSnd p i j PZX PNY sigma = toAmbientOver p i j PZY PZX := by
  apply Over.OverMorphism.ext
  exact pullback.lift_snd _ _ _

/-- The relative normal cone is a closed subscheme of the zero-section fiber of the
ambient normal-cone map. -/
theorem toZeroSectionFiber_isClosedImmersion :
    IsClosedImmersion (toZeroSectionFiber p i j PZY PZX PNY sigma e h_e).left := sorry

end ZeroSectionFiber

end AlgebraicGeometry.Scheme.NormalCone
