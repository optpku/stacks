module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.DeRham.Map
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous.Restrict
public import ReasLib.AlgebraicGeometry.RingedSite.Module.Pushforward
public import ReasLib.AlgebraicGeometry.RingedSpace.DeRham
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.OpensRingedSite
public import ReasLib.Topology.Sheaves.Algebraic.DeRham.DirectImage
public import Mathlib.CategoryTheory.CommSq
import Mathlib.Tactic.CrossRefAttribute

/-!
# Functoriality of relative de Rham complexes on ringed spaces

A commutative square of ringed spaces first induces a map between the inverse-image coefficient
sheaves.  This file makes that map, its associated morphism of coefficient ringed sites, and the
fixed-space de Rham map explicit.  These are the reusable data entering the canonical map into a
direct image complex.
-/

@[expose] public section

open CategoryTheory ComplexShape TopologicalSpace
open SheafOfModules.RingedSite

noncomputable section

universe u

namespace AlgebraicGeometry.RingedSpace.DeRham

variable {X' X S' S : RingedSpace.{u}}
variable {f : X' ⟶ X} {h' : X' ⟶ S'} {h : X ⟶ S} {g : S' ⟶ S}

/-- Pulling the base structure map around a commutative square gives a morphism
`f⁻¹h⁻¹𝒪_S ⟶ h'⁻¹𝒪_{S'}` on `X'`. -/
@[stacks 0FKQ "(2), inverse-image coefficient map"]
noncomputable def baseChangePullbackMap (sq : CommSq f h' h g) :
    (TopCat.Sheaf.pullback CommRingCat.{u} f.hom.base).obj (coefficients h) ⟶
      coefficients h' :=
  (RingedSpace.Hom.StructureSheaf.compIso f h).hom ≫
    (TopCat.Sheaf.pullbackCongr (A := CommRingCat.{u})
      (congrArg (fun k : X' ⟶ S ↦ k.hom.base) sq.w)).hom.app S.sheaf ≫
    (RingedSpace.Hom.StructureSheaf.compIso h' g).inv ≫
    (TopCat.Sheaf.pullback CommRingCat.{u} h'.hom.base).map (structureMap g)

/-- The coefficient morphism
`h⁻¹𝒪_S ⟶ f_*h'⁻¹𝒪_{S'}` adjoint to `baseChangePullbackMap`. -/
@[stacks 0FKQ "(2), coefficient map"]
noncomputable def baseChangeMap (sq : CommSq f h' h g) :
    coefficients h ⟶
      (TopCat.Sheaf.pushforward CommRingCat.{u} f.hom.base).obj (coefficients h') :=
  ((TopCat.Sheaf.pullbackPushforwardAdjunction CommRingCat.{u} f.hom.base).homEquiv _ _)
    (baseChangePullbackMap sq)

/-- The inverse adjunction bijection sends the coefficient map back to its explicit pullback
form. -/
@[stacks 0FKQ "adjunction specification for the coefficient map"]
theorem baseChangeMap_adj (sq : CommSq f h' h g) :
    ((TopCat.Sheaf.pullbackPushforwardAdjunction
      CommRingCat.{u} f.hom.base).homEquiv _ _).symm (baseChangeMap sq) =
      baseChangePullbackMap sq := sorry

/-- The relative structure maps form a commutative square after direct image along `f`. -/
@[stacks 0FKQ "relative structure square after direct image"]
theorem structureSquare (sq : CommSq f h' h g) :
    CommSq (baseChangeMap sq) (structureMap h)
      ((TopCat.Sheaf.pushforward CommRingCat.{u} f.hom.base).map (structureMap h'))
      (RingedSpace.Hom.commRingSheafPushforwardMap f) := sorry

/-- The coefficient ringed site associated to a morphism of ringed spaces. -/
abbrev coefficientSite {Y T : RingedSpace.{u}} (q : Y ⟶ T) :=
  RingedSite.ofCommRingSheaf (Opens.grothendieckTopology Y) (coefficients q)

/-- A commutative square of ringed spaces induces a morphism between its coefficient ringed
sites. -/
@[stacks 0FKQ "(2), coefficient ringed-site morphism"]
noncomputable def baseChangeHom (sq : CommSq f h' h g) :
    coefficientSite h' ⟶ coefficientSite h where
  base := Opens.map f.hom.base
  isMorphismOfSites := inferInstance
  structureSheafMap :=
    TopCat.Sheaf.ringSheafOfCommMap (baseChangeMap sq) ≫
      TopCat.Sheaf.commRingSheafPushforwardId f.hom.base (coefficients h')

/-- Direct image of modules along the coefficient morphism attached to a commutative square. -/
abbrev pushforward (sq : CommSq f h' h g) : Modules h' ⥤ Modules h :=
  RingedSite.Hom.modulePushforward (baseChangeHom sq)

/-- Direct image along the coefficient morphism is additive. -/
instance pushforward_additive (sq : CommSq f h' h g) : (pushforward sq).Additive := sorry

/-- Direct image of cochain complexes along the coefficient morphism. -/
abbrev pushforwardComplex (sq : CommSq f h' h g) :=
  (pushforward sq).mapHomologicalComplex (up ℕ)

/-- Restriction of module sheaves along the coefficient map of a commutative square. -/
abbrev coefficientRestriction (sq : CommSq f h' h g) :
    SheafOfModules
        (TopCat.Sheaf.ringSheafOfComm
          ((TopCat.Sheaf.pushforward CommRingCat.{u} f.hom.base).obj
            (coefficients h'))) ⥤
      Modules h :=
  restrictionAlong (J := Opens.grothendieckTopology X)
    (baseChangeMap (f := f) (h' := h') (h := h) (g := g) sq)

/-- The two-stage module direct image: first along the underlying continuous map, then by
restriction along the coefficient map of the commutative square. -/
abbrev stagedPushforward (sq : CommSq f h' h g) : Modules h' ⥤ Modules h :=
  TopCat.Sheaf.DeRham.DirectImage.modules f.hom.base (coefficients h') ⋙
    coefficientRestriction sq

/-- The composite ring-sheaf map defining the staged direct image agrees with the structure map
of the coefficient ringed-site morphism. -/
theorem stagedStructureMap (sq : CommSq f h' h g) :
    SheafOfModules.ChangeOfRings.homOverId
          (TopCat.Sheaf.ringSheafOfCommMap
            (baseChangeMap (f := f) (h' := h') (h := h) (g := g) sq)) ≫
        ((𝟭 (Opens X)).sheafPushforwardContinuous RingCat.{u}
          (Opens.grothendieckTopology X) (Opens.grothendieckTopology X)).map
          (TopCat.Sheaf.commRingSheafPushforwardId
            f.hom.base (coefficients h')) =
      (baseChangeHom sq).structureSheafMap := sorry

/-- The two-stage direct image is canonically isomorphic to module direct image along the
coefficient ringed-site morphism. -/
@[stacks 0FKQ "(2), module pushforward comparison"]
noncomputable def pushforwardIso (sq : CommSq f h' h g) :
    stagedPushforward sq ≅ pushforward sq :=
  SheafOfModules.pushforwardRestrictIso
      (TopCat.Sheaf.ringSheafOfCommMap
        (baseChangeMap (f := f) (h' := h') (h := h) (g := g) sq))
      (TopCat.Sheaf.commRingSheafPushforwardId f.hom.base (coefficients h')) ≪≫
    SheafOfModules.pushforwardCongr (stagedStructureMap sq)

/-- The canonical comparison between the corresponding two-stage and one-stage direct images
of cochain complexes. -/
@[stacks 0FKQ "complex pushforward comparison"]
noncomputable def pushforwardComplexIso (sq : CommSq f h' h g) :
    (TopCat.Sheaf.DeRham.DirectImage.complexes f.hom.base (coefficients h') ⋙
        (coefficientRestriction sq).mapHomologicalComplex (up ℕ)) ≅
      pushforwardComplex sq :=
  Functor.mapHomologicalComplexCompIso
      (F := TopCat.Sheaf.DeRham.DirectImage.modules f.hom.base (coefficients h'))
      (G := coefficientRestriction sq) (H := stagedPushforward sq)
      (Iso.refl (stagedPushforward sq)) (up ℕ) ≪≫
    NatIso.mapHomologicalComplex (pushforwardIso sq) (up ℕ)

variable [HasWeakSheafify (Opens.grothendieckTopology X) AddCommGrpCat]
variable [(Opens.grothendieckTopology X).WEqualsLocallyBijective AddCommGrpCat]

/-- The fixed-space de Rham map induced by the commutative square of direct-image ring sheaves. -/
@[stacks 0FKQ "(2), fixed-space de Rham map"]
noncomputable def fixedMap (sq : CommSq f h' h g) :
    complex h ⟶
      (SheafOfModules.RingedSite.DeRham.complexRestriction
        (baseChangeMap sq)).obj
        (TopCat.Sheaf.DeRham.complex
          ((TopCat.Sheaf.pushforward CommRingCat.{u} f.hom.base).map (structureMap h'))) :=
  SheafOfModules.RingedSite.DeRham.map
    (J := Opens.grothendieckTopology X) (structureSquare sq)

/-- The degree-`p` component of the fixed-space comparison is the corresponding ringed-site de
Rham map. -/
@[simp, stacks 0FKQ "degreewise component of the fixed-space de Rham map"]
theorem fixedMap_f (sq : CommSq f h' h g) (p : ℕ) :
    (fixedMap sq).f p =
      SheafOfModules.RingedSite.DeRham.mapApp (structureSquare sq) p := sorry

variable [HasWeakSheafify (Opens.grothendieckTopology X') AddCommGrpCat]
variable [(Opens.grothendieckTopology X').WEqualsLocallyBijective AddCommGrpCat]

/-- Definition 17.30.4 (0FKQ) (2): a commutative square of ringed spaces induces the canonical
map `Ωᵈᴿ[h] ⟶ f_* Ωᵈᴿ[h']` of relative de Rham complexes. -/
@[stacks 0FKQ "(2)"]
noncomputable def map (sq : CommSq f h' h g) :
    complex h ⟶ (pushforwardComplex sq).obj (complex h') :=
  fixedMap sq ≫
    ((coefficientRestriction sq).mapHomologicalComplex (up ℕ)).map
      (TopCat.Sheaf.DeRham.DirectImage.map f.hom.base (structureMap h')) ≫
    (pushforwardComplexIso sq).hom.app (complex h')

/-- The degree-`p` component of the relative de Rham base-change map. -/
@[simp, stacks 0FKQ "degreewise component of the relative de Rham base-change map"]
theorem map_f (sq : CommSq f h' h g) (p : ℕ) :
    (map sq).f p =
      SheafOfModules.RingedSite.DeRham.mapApp (structureSquare sq) p ≫
        (coefficientRestriction sq).map
          (TopCat.Sheaf.DeRham.DirectImage.mapApp
            f.hom.base (structureMap h') p) ≫
        ((pushforwardComplexIso sq).hom.app (complex h')).f p := sorry

end AlgebraicGeometry.RingedSpace.DeRham
