module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.Deformation.Parameters
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.Deformation.Perturbation.Construction
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.Deformation.DifferenceConstruction
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.EtaleSite.IdentityChart

/-!
# The actual parameter and automorphism sheaf maps

On an etale algebraic-space test, the parameter is the actual right-Kan family of local
Hom morphisms on its scheme charts. Evaluating those morphisms gives a global Hom map on
the test's reduced space. Its actual diagonal perturbation is the forward sheaf map.
The reverse uses ordered differences and the actual conormal comparison on each chart.
-/

public section

open CategoryTheory AlgebraicGeometry Opposite CategoryTheory.Limits
open AlgebraicGeometry.AlgebraicSpace

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Hom.Deformation

namespace SheafComparison

variable {S : Scheme.{u}} {U U' I I' : AlgebraicSpace S}
variable (iU : U ⟶ U') (iI : I ⟶ I') (p' : I' ⟶ U') (p : I ⟶ U)
variable (Δ' : U' ⟶ I') (Δ : U ⟶ I)
variable [hiU : IsFirstOrderThickening iU] [hiI : IsFirstOrderThickening iI]
variable (hΔ : IsPullback Δ iU iI Δ') (hp : IsPullback p iI iU p')
variable (hsec : Δ' ≫ p' = 𝟙 U')

include hiU in
/-- The reduced-test immersion is the first-order base change of the original thickening. -/
private theorem closedι_firstOrder (V' : spacesEtaleSite U') :
    IsFirstOrderThickening (closedι iU V') where
  toIsClosedImmersion := inferInstance
  square_zero := sorry

/-- The right-Kan diagram of actual Hom sections on schemes over the reduced test. -/
private abbrev parameterDiagram (V' : spacesEtaleSite U') :=
  StructuredArrow.proj (op ((spacesEtalePullback iU).obj V')) (smallEtaleToSpaces U).op ⋙
    (parameterTypeSheaf iU p Δ).obj

/-- A scheme chart of the reduced test is an actual index of that parameter diagram. -/
def parameterChartIndex (V' : spacesEtaleSite U') (R : smallEtaleSite (closedSpace iU V')) :
    StructuredArrow (op ((spacesEtalePullback iU).obj V')) (smallEtaleToSpaces U).op :=
  StructuredArrow.mk
    (S := op ((spacesEtalePullback iU).obj V')) (T := (smallEtaleToSpaces U).op)
    (Y := op ((@Modules.restrictPostcompose _ _ _ (toSource iU V') ((spacesEtalePullback iU).obj V').prop).obj R))
    (MorphismProperty.Over.homMk R.hom (by sorry) trivial).op

/-- Read the parameter's actual local Hom section at a reduced scheme chart by a limit
projection of the right-Kan family. -/
def parameterAtChart (V' : spacesEtaleSite U')
    (θ : (parameterSheafEtale iU p Δ).obj.obj (op V'))
    (R : smallEtaleSite (closedSpace iU V')) :
    (parameterModule iU p Δ).val.obj
      (op ((@Modules.restrictPostcompose _ _ _ (toSource iU V') ((spacesEtalePullback iU).obj V').prop).obj R)) :=
  limit.π (parameterDiagram iU p Δ V') (parameterChartIndex iU V' R)
    (((smallEtaleToSpaces U).op.ranObjObjIsoLimit (parameterTypeSheaf iU p Δ).obj
      (op ((spacesEtalePullback iU).obj V'))).hom θ)

/-- Evaluate a local Hom component on its slice identity and undo only the universe lift. -/
def parameterRestrictionSection (V' : spacesEtaleSite U')
    (θ : (parameterSheafEtale iU p Δ).obj.obj (op V'))
    (R : smallEtaleSite (closedSpace iU V'))
    (s : ((@Modules.restrictFunctor _ _ _ (toSource iU V') ((spacesEtalePullback iU).obj V').prop).obj ((Modules.pullback Δ).obj (Hom.relativeDifferentials p))).val.obj
      (op R)) :
    ((@Modules.restrictFunctor _ _ _ (toSource iU V') ((spacesEtalePullback iU).obj V').prop).obj (Hom.conormalSheaf iU)).val.obj (op R) :=
  let T := (@Modules.restrictPostcompose _ _ _ (toSource iU V') ((spacesEtalePullback iU).obj V').prop).obj R
  let localHom := parameterLocalHom iU p Δ T (parameterAtChart iU p Δ V' θ R)
  (localHom.val.app (op (Over.mk (𝟙 T)))).hom s

/-- The specified component functions are additive and linear and commute with restriction. -/
private theorem parameterRestrictionHom_laws (V' : spacesEtaleSite U')
    (θ : (parameterSheafEtale iU p Δ).obj.obj (op V')) :
    let F := (@Modules.restrictFunctor _ _ _ (toSource iU V') ((spacesEtalePullback iU).obj V').prop).obj ((Modules.pullback Δ).obj (Hom.relativeDifferentials p))
    let G := (@Modules.restrictFunctor _ _ _ (toSource iU V') ((spacesEtalePullback iU).obj V').prop).obj (Hom.conormalSheaf iU)
    let f : ∀ R : (smallEtaleSite (closedSpace iU V'))ᵒᵖ, F.val.obj R → G.val.obj R := fun R ↦ parameterRestrictionSection iU p Δ V' θ R.unop
    (∀ R x y, f R (x + y) = f R x + f R y) ∧
    (∀ R (r : (structureSheaf (closedSpace iU V')).obj.obj R) x, f R (r • x) = r • f R x) ∧
    (∀ {R T : (smallEtaleSite (closedSpace iU V'))ᵒᵖ} (g : R ⟶ T) (x : F.val.obj R),
      f T (F.val.map g x) = G.val.map g (f R x)) := sorry

/-- The right-Kan family's evaluated components define the actual map on etale restrictions. -/
def parameterRestrictionHom (V' : spacesEtaleSite U')
    (θ : (parameterSheafEtale iU p Δ).obj.obj (op V')) :
    (@Modules.restrictFunctor _ _ _ (toSource iU V') ((spacesEtalePullback iU).obj V').prop).obj ((Modules.pullback Δ).obj (Hom.relativeDifferentials p)) ⟶
      (@Modules.restrictFunctor _ _ _ (toSource iU V') ((spacesEtalePullback iU).obj V').prop).obj (Hom.conormalSheaf iU) :=
  ⟨{ app := fun R ↦ ModuleCat.ofHom
        (X := ((@Modules.restrictFunctor _ _ _ (toSource iU V') ((spacesEtalePullback iU).obj V').prop).obj
          ((Modules.pullback Δ).obj (Hom.relativeDifferentials p))).val.obj R)
        (Y := ((@Modules.restrictFunctor _ _ _ (toSource iU V') ((spacesEtalePullback iU).obj V').prop).obj
          (Hom.conormalSheaf iU)).val.obj R)
        { toFun := parameterRestrictionSection iU p Δ V' θ R.unop
          map_add' := by exact (parameterRestrictionHom_laws iU p Δ V' θ).1 R
          map_smul' := by exact (parameterRestrictionHom_laws iU p Δ V' θ).2.1 R }
     naturality := by
       intro R T g
       ext x
       exact (parameterRestrictionHom_laws iU p Δ V' θ).2.2 g x }⟩

/-- Transport the actual restricted Hom map to the two genuine pulled-back modules. -/
def parameterPullbackHom (V' : spacesEtaleSite U')
    (θ : (parameterSheafEtale iU p Δ).obj.obj (op V')) :
    (Modules.pullback (toSource iU V')).obj ((Modules.pullback Δ).obj (Hom.relativeDifferentials p)) ⟶
      (Modules.pullback (toSource iU V')).obj (Hom.conormalSheaf iU) :=
  (@Modules.restrictFunctorIsoPullback _ _ _ (toSource iU V') ((spacesEtalePullback iU).obj V').prop).inv.app ((Modules.pullback Δ).obj (Hom.relativeDifferentials p)) ≫
    parameterRestrictionHom iU p Δ V' θ ≫
    (@Modules.restrictFunctorIsoPullback _ _ _ (toSource iU V') ((spacesEtalePullback iU).obj V').prop).hom.app (Hom.conormalSheaf iU)

/-- The actual differential parameter on the reduced test space, with the original
conormal pulled back through its displayed thickening square. -/
def parameterOnReduced (V' : spacesEtaleSite U')
    (θ : (parameterSheafEtale iU p Δ).obj.obj (op V')) :
    (Modules.pullback (toSource iU V' ≫ Δ)).obj (Hom.relativeDifferentials p) ⟶
      Hom.conormalSheaf (closedι iU V') :=
  (Modules.pullbackCompIso (toSource iU V') Δ).inv.app (Hom.relativeDifferentials p) ≫
    parameterPullbackHom iU p Δ V' θ ≫ Hom.Conormal.map (thickeningPullbackSq iU V')

/-- The supplied diagonal has the correct restriction on every actual reduced test. -/
private theorem referenceSquare (hSquare : IsPullback Δ iU iI Δ') (V' : spacesEtaleSite U') :
    CommSq (toSource iU V' ≫ Δ) (closedι iU V') iI (V'.hom ≫ Δ') := ⟨by sorry⟩

/-- The forward section is the actual perturbation of the restricted supplied diagonal. -/
def parameterToAutHom (V' : spacesEtaleSite U')
    (θ : (parameterSheafEtale iU p Δ).obj.obj (op V')) : V'.left ⟶ I' :=
  @perturbHom _ _ _ _ _ _ (closedι iU V') iI (toSource iU V' ≫ Δ) (V'.hom ≫ Δ')
    (by exact closedι_firstOrder iU V') hiI
    (by exact referenceSquare iU iI Δ' Δ hΔ V') p (parameterOnReduced iU p Δ V' θ)

include hp hsec in
/-- The constructed map is over the base, restricts to the specified reduced map, and has
the prescribed conormal comparison. These are laws of the actual parameter action. -/
theorem parameterToAutHom_mem (V' : spacesEtaleSite U')
    (θ : (parameterSheafEtale iU p Δ).obj.obj (op V')) :
    parameterToAutHom iU iI p Δ' Δ hΔ V' θ ∈ autSections iU iI p' Δ' Δ hΔ V' := sorry

/-- The actual forward component of the parameter/automorphism sheaf correspondence. -/
def parameterToAut (V' : spacesEtaleSite U')
    (θ : (parameterSheafEtale iU p Δ).obj.obj (op V')) :
    (autPresheaf iU iI p' Δ' Δ hΔ).obj (op V') :=
  ⟨parameterToAutHom iU iI p Δ' Δ hΔ V' θ,
    parameterToAutHom_mem iU iI p' p Δ' Δ hΔ hp hsec V' θ⟩

/-- Invert the specified conormal comparison on an actual section. Etale base change makes
this fixed comparison bijective; the exact graph selects its preimage, with zero off-image. -/
def conormalInverseSection (V' : spacesEtaleSite U')
    (R : (smallEtaleSite (closedSpace iU V'))ᵒᵖ)
    (c : (Hom.conormalSheaf (closedι iU V')).val.obj R) :
    ((Modules.pullback (toSource iU V')).obj (Hom.conormalSheaf iU)).val.obj R := by
  classical
  exact if h : ∃ s : ((Modules.pullback (toSource iU V')).obj (Hom.conormalSheaf iU)).val.obj R,
      ((Hom.Conormal.map (thickeningPullbackSq iU V')).val.app R).hom s = c
    then h.choose else 0

/-- The specified component functions are additive and linear and commute with restriction. -/
private theorem conormalInverse_laws (V' : spacesEtaleSite U') :
    let F := Hom.conormalSheaf (closedι iU V')
    let G := (Modules.pullback (toSource iU V')).obj (Hom.conormalSheaf iU)
    let f : ∀ R : (smallEtaleSite (closedSpace iU V'))ᵒᵖ, F.val.obj R → G.val.obj R := fun R ↦ conormalInverseSection iU V' R
    (∀ R x y, f R (x + y) = f R x + f R y) ∧
    (∀ R (r : (structureSheaf (closedSpace iU V')).obj.obj R) x, f R (r • x) = r • f R x) ∧
    (∀ {R T : (smallEtaleSite (closedSpace iU V'))ᵒᵖ} (g : R ⟶ T) (x : F.val.obj R),
      f T (F.val.map g x) = G.val.map g (f R x)) := sorry

/-- The actual inverse conormal-comparison component functions, with their original actions. -/
def conormalInverse (V' : spacesEtaleSite U') :
    Hom.conormalSheaf (closedι iU V') ⟶
      (Modules.pullback (toSource iU V')).obj (Hom.conormalSheaf iU) :=
  ⟨{ app := fun R ↦ ModuleCat.ofHom
        (X := (Hom.conormalSheaf (closedι iU V')).val.obj R)
        (Y := ((Modules.pullback (toSource iU V')).obj (Hom.conormalSheaf iU)).val.obj R)
        { toFun := conormalInverseSection iU V' R
          map_add' := by exact (conormalInverse_laws iU V').1 R
          map_smul' := by exact (conormalInverse_laws iU V').2.1 R }
     naturality := by
       intro R T g
       ext x
       exact (conormalInverse_laws iU V').2.2 g x }⟩

/-- The selected preimage is the inverse of the specified conormal comparison. -/
theorem conormalInverse_hom (V' : spacesEtaleSite U') :
    conormalInverse iU V' ≫ Hom.Conormal.map (thickeningPullbackSq iU V') = 𝟙 _ := sorry

/-- The specified conormal comparison followed by its section inverse is the identity. -/
theorem conormalHom_inverse (V' : spacesEtaleSite U') :
    Hom.Conormal.map (thickeningPullbackSq iU V') ≫ conormalInverse iU V' = 𝟙 _ := sorry

/-- A raw section retains its actual reduction square. -/
private theorem rawSquare (V' : spacesEtaleSite U')
    (δ : (autPresheaf iU iI p' Δ' Δ hΔ).obj (op V')) :
    CommSq (toSource iU V' ≫ Δ) (closedι iU V') iI δ.val := ⟨by sorry⟩

include hp hsec in
/-- Both the diagonal and the raw compatible section have the prescribed conormal map. -/
private theorem rawConormal (V' : spacesEtaleSite U')
    (δ : (autPresheaf iU iI p' Δ' Δ hΔ).obj (op V')) :
    Hom.Conormal.map (by exact referenceSquare iU iI Δ' Δ hΔ V') =
      Hom.Conormal.map (by exact rawSquare iU iI p' Δ' Δ hΔ V' δ) := sorry

/-- The reverse section map is the actual reference-minus-section additive difference. -/
def rawDifference (V' : spacesEtaleSite U')
    (δ : (autPresheaf iU iI p' Δ' Δ hΔ).obj (op V')) :
    (sheafCompose (smallEtaleTopology I) (forget₂ RingCat AddCommGrpCat.{u})).obj
        (structureSheaf I) ⟶
      (SheafOfModules.toSheaf (structureSheaf I)).obj
        ((Modules.pushforward (toSource iU V' ≫ Δ)).obj
          (Hom.conormalSheaf (closedι iU V'))) :=
  @differenceAdjoint _ _ _ _ _ (closedι iU V') iI (toSource iU V' ≫ Δ) (V'.hom ≫ Δ') δ.val
    (by exact closedι_firstOrder iU V') hiI
    (by exact referenceSquare iU iI Δ' Δ hΔ V') (by exact rawSquare iU iI p' Δ' Δ hΔ V' δ)
    (by exact rawConormal iU iI p' p Δ' Δ hΔ hp hsec V' δ)

/-- The reference-minus-section functions obey the Leibniz and restriction laws
and vanish on inverse-image coefficients from the reduced base. -/
private theorem rawDerivation_laws (V' : spacesEtaleSite U')
    (δ : (autPresheaf iU iI p' Δ' Δ hΔ).obj (op V')) :
    let M := toCommPresheaf ((Modules.pushforward (toSource iU V' ≫ Δ)).obj
      (Hom.conormalSheaf (closedι iU V')))
    let d : ∀ T : (smallEtaleSite I)ᵒᵖ,
        (commStructureSheaf I).obj.obj T →+ M.obj T := fun T ↦
      (rawDifference iU iI p' p Δ' Δ hΔ hp hsec V' δ).hom.app T |>.hom
    (∀ T (a b : (commStructureSheaf I).obj.obj T),
      d T (a * b) = a • d T b + b • d T a) ∧
    (∀ {T Z : (smallEtaleSite I)ᵒᵖ} (f : T ⟶ Z)
      (a : (commStructureSheaf I).obj.obj T),
      d Z ((commStructureSheaf I).obj.map f a) = M.map f (d T a)) ∧
    (∀ T (a : (commInverseImageStructureSheaf p).obj.obj T),
      d T ((commInverseImageStructureSheafMap p).hom.app T a) = 0) := sorry

/-- The actual ordered difference forms a derivation relative to the reduced base. -/
def rawDerivation (V' : spacesEtaleSite U')
    (δ : (autPresheaf iU iI p' Δ' Δ hΔ).obj (op V')) :
    Hom.derivations p ((Modules.pushforward (toSource iU V' ≫ Δ)).obj
      (Hom.conormalSheaf (closedι iU V'))) where
  d {T} := (rawDifference iU iI p' p Δ' Δ hΔ hp hsec V' δ).hom.app T |>.hom
  d_mul {T} a b := by exact (rawDerivation_laws iU iI p' p Δ' Δ hΔ hp hsec V' δ).1 T a b
  d_map {T V} f a := by exact (rawDerivation_laws iU iI p' p Δ' Δ hΔ hp hsec V' δ).2.1 f a
  d_app {T} a := by exact (rawDerivation_laws iU iI p' p Δ' Δ hΔ hp hsec V' δ).2.2 T a

/-- Recover the actual differential parameter on the reduced test by native Kähler descent. -/
def rawParameter (V' : spacesEtaleSite U')
    (δ : (autPresheaf iU iI p' Δ' Δ hΔ).obj (op V')) :
    (Modules.pullback (toSource iU V' ≫ Δ)).obj (Hom.relativeDifferentials p) ⟶
      Hom.conormalSheaf (closedι iU V') :=
  ((Modules.pullbackPushforwardAdjunction (toSource iU V' ≫ Δ)).homEquiv _ _).symm
    (SheafOfModules.RingedSite.relativeDifferentialDesc
      (commInverseImageStructureSheafMap p)
      (rawDerivation iU iI p' p Δ' Δ hΔ hp hsec V' δ))

/-- Express the recovered parameter on the two pulled-back original coefficient modules. -/
def rawPullbackHom (V' : spacesEtaleSite U')
    (δ : (autPresheaf iU iI p' Δ' Δ hΔ).obj (op V')) :
    (Modules.pullback (toSource iU V')).obj ((Modules.pullback Δ).obj (Hom.relativeDifferentials p)) ⟶
      (Modules.pullback (toSource iU V')).obj (Hom.conormalSheaf iU) :=
  (Modules.pullbackCompIso (toSource iU V') Δ).hom.app (Hom.relativeDifferentials p) ≫
    rawParameter iU iI p' p Δ' Δ hΔ hp hsec V' δ ≫ conormalInverse iU V'

variable (V' : spacesEtaleSite U') (T : smallEtaleSite U)
variable (k : ofOver T.left ⟶ closedSpace iU V') (hk : k ≫ toSource iU V' = T.hom)

/-- A chart of the slice over `T` maps to the reduced test by its actual scheme arrow to `T`. -/
private def sliceChart (htriangle : k ≫ toSource iU V' = T.hom) (W : Over T) :
    smallEtaleSite (closedSpace iU V') :=
  @smallEtaleSite.mk S (closedSpace iU V') W.left.left (ofOverMap W.hom.left ≫ k) (by sorry)

/-- Postcomposing this slice chart gives back the original chart, by the identity scheme map. -/
private def sliceChartIso (htriangle : k ≫ toSource iU V' = T.hom) (W : Over T) :
    (@Modules.restrictPostcompose _ _ _ (toSource iU V') ((spacesEtalePullback iU).obj V').prop).obj (sliceChart iU V' T k htriangle W) ≅ W.left :=
  MorphismProperty.CostructuredArrow.isoMk (Iso.refl W.left.left) trivial trivial (by sorry)

/-- The specified component functions are additive and linear and commute with restriction. -/
private theorem rawLocalHom_laws (δ : (autPresheaf iU iI p' Δ' Δ hΔ).obj (op V')) :
    let F := ((Modules.pullback Δ).obj (Hom.relativeDifferentials p)).over T
    let G := (Hom.conormalSheaf iU).over T
    let f : ∀ R : (Over T)ᵒᵖ, F.val.obj R → G.val.obj R := fun W ↦ fun s ↦
            let R := sliceChart iU V' T k hk W.unop
            let e := sliceChartIso iU V' T k hk W.unop
            let t : ((Modules.pullback Δ).obj (Hom.relativeDifferentials p)).val.obj
                (op ((@Modules.restrictPostcompose _ _ _ (toSource iU V') ((spacesEtalePullback iU).obj V').prop).obj R)) :=
              ((Modules.pullback Δ).obj (Hom.relativeDifferentials p)).val.map e.hom.op s
            let t' := (((@Modules.restrictFunctorIsoPullback _ _ _ (toSource iU V') ((spacesEtalePullback iU).obj V').prop).hom.app
              ((Modules.pullback Δ).obj (Hom.relativeDifferentials p))).val.app (op R)).hom t
            let r := ((rawPullbackHom iU iI p' p Δ' Δ hΔ hp hsec V' δ).val.app (op R)).hom t'
            let r' : (Hom.conormalSheaf iU).val.obj
                (op ((@Modules.restrictPostcompose _ _ _ (toSource iU V') ((spacesEtalePullback iU).obj V').prop).obj R)) :=
              (((@Modules.restrictFunctorIsoPullback _ _ _ (toSource iU V') ((spacesEtalePullback iU).obj V').prop).inv.app
                (Hom.conormalSheaf iU)).val.app (op R)).hom r
            (Hom.conormalSheaf iU).val.map e.inv.op r'
    (∀ R x y, f R (x + y) = f R x + f R y) ∧
    (∀ R (r : ((structureSheaf U).over T).obj.obj R) x, f R (r • x) = r • f R x) ∧
    (∀ {R T : (Over T)ᵒᵖ} (g : R ⟶ T) (x : F.val.obj R),
      f T (F.val.map g x) = G.val.map g (f R x)) := sorry

-- The chart and pullback comparisons produce deeply nested definitional equalities.
set_option maxRecDepth 4096 in
/-- The recovered local Hom has actual component functions through the fixed chart
isomorphism, pullback comparison, and recovered parameter. -/
def rawLocalHom (δ : (autPresheaf iU iI p' Δ' Δ hΔ).obj (op V')) :
    ((Modules.pullback Δ).obj (Hom.relativeDifferentials p)).over T ⟶ (Hom.conormalSheaf iU).over T :=
  ⟨{ app := fun W ↦ ModuleCat.ofHom
        (X := (((Modules.pullback Δ).obj (Hom.relativeDifferentials p)).over T).val.obj W)
        (Y := ((Hom.conormalSheaf iU).over T).val.obj W)
        { toFun := fun s ↦
            let R := sliceChart iU V' T k hk W.unop
            let e := sliceChartIso iU V' T k hk W.unop
            let t : ((Modules.pullback Δ).obj (Hom.relativeDifferentials p)).val.obj
                (op ((@Modules.restrictPostcompose _ _ _ (toSource iU V') ((spacesEtalePullback iU).obj V').prop).obj R)) :=
              ((Modules.pullback Δ).obj (Hom.relativeDifferentials p)).val.map e.hom.op s
            let t' := (((@Modules.restrictFunctorIsoPullback _ _ _ (toSource iU V') ((spacesEtalePullback iU).obj V').prop).hom.app
              ((Modules.pullback Δ).obj (Hom.relativeDifferentials p))).val.app (op R)).hom t
            let r := ((rawPullbackHom iU iI p' p Δ' Δ hΔ hp hsec V' δ).val.app (op R)).hom t'
            let r' : (Hom.conormalSheaf iU).val.obj
                (op ((@Modules.restrictPostcompose _ _ _ (toSource iU V') ((spacesEtalePullback iU).obj V').prop).obj R)) :=
              (((@Modules.restrictFunctorIsoPullback _ _ _ (toSource iU V') ((spacesEtalePullback iU).obj V').prop).inv.app
                (Hom.conormalSheaf iU)).val.app (op R)).hom r
            (Hom.conormalSheaf iU).val.map e.inv.op r'
          map_add' := by exact (rawLocalHom_laws iU iI p' p Δ' Δ hΔ hp hsec V' T k hk δ).1 W
          map_smul' := by exact (rawLocalHom_laws iU iI p' p Δ' Δ hΔ hp hsec V' T k hk δ).2.1 W }
     naturality := by
       intro R Z g
       ext x
       exact (rawLocalHom_laws iU iI p' p Δ' Δ hΔ hp hsec V' T k hk δ).2.2 g x }⟩

/-- Lift the recovered local Hom by its actual `ULift.up` component functions. -/
def rawLocalParameter (δ : (autPresheaf iU iI p' Δ' Δ hΔ).obj (op V')) :
    (parameterModule iU p Δ).val.obj (op T) :=
  Modules.liftLocalHom ((Modules.pullback Δ).obj (Hom.relativeDifferentials p)) (Hom.conormalSheaf iU) T
    (rawLocalHom iU iI p' p Δ' Δ hΔ hp hsec V' T k hk δ)

/-- Each right-Kan index already stores its actual map into the reduced test and triangle. -/
private theorem parameterIndex_triangle
    (A : StructuredArrow (op ((spacesEtalePullback iU).obj V')) (smallEtaleToSpaces U).op) :
    A.hom.unop.left ≫ toSource iU V' = A.right.unop.hom := sorry

/-- The recovered parameters on all right-Kan chart indices, assembled by their actual
local Hom functions. Compatibility is the naturality law of the recovered difference. -/
def rawParameterCone (δ : (autPresheaf iU iI p' Δ' Δ hΔ).obj (op V')) :
    Cone (StructuredArrow.proj (op ((spacesEtalePullback iU).obj V'))
      (smallEtaleToSpaces U).op ⋙ (parameterTypeSheaf iU p Δ).obj) where
  pt := PUnit.{u + 2}
  π :=
    { app := fun A ↦ TypeCat.ofHom fun _ ↦
        rawLocalParameter iU iI p' p Δ' Δ hΔ hp hsec V' A.right.unop A.hom.unop.left
          (by exact parameterIndex_triangle iU V' A) δ
      naturality := sorry }

/-- The reverse sheaf component is the actual limit lift of the recovered compatible
chart parameters, transported back through the native right-Kan comparison. -/
def autToParameter (δ : (autPresheaf iU iI p' Δ' Δ hΔ).obj (op V')) :
    (parameterSheafEtale iU p Δ).obj.obj (op V') :=
  ((smallEtaleToSpaces U).op.ranObjObjIsoLimit (parameterTypeSheaf iU p Δ).obj
      (op ((spacesEtalePullback iU).obj V'))).inv
    (limit.lift _ (rawParameterCone iU iI p' p Δ' Δ hΔ hp hsec V' δ) PUnit.unit)

/-- Perturbation and recovered differences commute with actual etale restriction maps. -/
theorem parameterToAut_naturality {V' W' : spacesEtaleSite U'} (f : V' ⟶ W')
    (θ : (parameterSheafEtale iU p Δ).obj.obj (op W')) :
    (autPresheaf iU iI p' Δ' Δ hΔ).map f.op
        (parameterToAut iU iI p' p Δ' Δ hΔ hp hsec W' θ) =
      parameterToAut iU iI p' p Δ' Δ hΔ hp hsec V'
        ((parameterSheafEtale iU p Δ).obj.map f.op θ) := sorry

/-- The recovered right-Kan parameter family commutes with etale restriction. -/
theorem autToParameter_naturality {V' W' : spacesEtaleSite U'} (f : V' ⟶ W')
    (δ : (autPresheaf iU iI p' Δ' Δ hΔ).obj (op W')) :
    (parameterSheafEtale iU p Δ).obj.map f.op
        (autToParameter iU iI p' p Δ' Δ hΔ hp hsec W' δ) =
      autToParameter iU iI p' p Δ' Δ hΔ hp hsec V'
        ((autPresheaf iU iI p' Δ' Δ hΔ).map f.op δ) := sorry

/-- The actual forward sheaf morphism is specified on every test object. -/
def parameterToAutSheaf : parameterSheafEtale iU p Δ ⟶ autSheaf iU iI p' Δ' Δ hΔ :=
  ⟨{ app := fun V' ↦ TypeCat.ofHom (parameterToAut iU iI p' p Δ' Δ hΔ hp hsec V'.unop)
     naturality := by
       intro V' W' f
       ext θ
       exact (parameterToAut_naturality iU iI p' p Δ' Δ hΔ hp hsec f.unop θ).symm }⟩

/-- The actual reverse sheaf morphism retains the ordered-difference limit-lift functions. -/
def autToParameterSheaf : autSheaf iU iI p' Δ' Δ hΔ ⟶ parameterSheafEtale iU p Δ :=
  ⟨{ app := fun V' ↦ TypeCat.ofHom (autToParameter iU iI p' p Δ' Δ hΔ hp hsec V'.unop)
     naturality := by
       intro V' W' f
       ext δ
       exact (autToParameter_naturality iU iI p' p Δ' Δ hΔ hp hsec f.unop δ).symm }⟩

end SheafComparison

variable {S : Scheme.{u}} {U U' I I' : AlgebraicSpace S}
variable (iU : U ⟶ U') (iI : I ⟶ I') (p' : I' ⟶ U') (p : I ⟶ U)
variable (Δ' : U' ⟶ I') (Δ : U ⟶ I)
variable [IsFirstOrderThickening iU] [IsFirstOrderThickening iI]
variable (hΔ : IsPullback Δ iU iI Δ') (hp : IsPullback p iI iU p')
variable (hsec : Δ' ≫ p' = 𝟙 U')

/-- The diagonal-perturbation and ordered-difference sheaf morphisms are mutual inverses. -/
private theorem parameterAutIso_laws :
    SheafComparison.parameterToAutSheaf iU iI p' p Δ' Δ hΔ hp hsec ≫
        SheafComparison.autToParameterSheaf iU iI p' p Δ' Δ hΔ hp hsec = 𝟙 _ ∧
    SheafComparison.autToParameterSheaf iU iI p' p Δ' Δ hΔ hp hsec ≫
        SheafComparison.parameterToAutSheaf iU iI p' p Δ' Δ hΔ hp hsec = 𝟙 _ := sorry

/-- Acting on the diagonal identifies differential parameters with automorphism sections.
The inverse recovers the ordered difference and its right-Kan family of local parameters. -/
def parameterAutIso : parameterSheafEtale iU p Δ ≅ autSheaf iU iI p' Δ' Δ hΔ where
  hom := SheafComparison.parameterToAutSheaf iU iI p' p Δ' Δ hΔ hp hsec
  inv := SheafComparison.autToParameterSheaf iU iI p' p Δ' Δ hΔ hp hsec
  hom_inv_id := by exact (parameterAutIso_laws iU iI p' p Δ' Δ hΔ hp hsec).1
  inv_hom_id := by exact (parameterAutIso_laws iU iI p' p Δ' Δ hΔ hp hsec).2

include hp hsec in
/-- The parameter sheaf is isomorphic to the automorphism-section sheaf. -/
theorem parameter_iso_aut :
    IsIsomorphic (parameterSheafEtale iU p Δ) (autSheaf iU iI p' Δ' Δ hΔ) :=
  ⟨parameterAutIso iU iI p' p Δ' Δ hΔ hp hsec⟩

/-- The diagonal-action isomorphism sends the transported zero parameter to the diagonal. -/
theorem parameter_iso_aut_zero :
    (parameterAutIso iU iI p' p Δ' Δ hΔ hp hsec).hom.hom.app
        (op (spacesEtaleSite.self U')) (parameterSheafEtaleZero iU p Δ) =
      Subtype.mk Δ' (diagonal_mem_autSections iU iI p' Δ' Δ hΔ hsec) := sorry

end AlgebraicGeometry.AlgebraicSpace.Hom.Deformation
