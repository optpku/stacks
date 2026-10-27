/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Yoneda
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Pullback
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.RelativeProj.BaseChange

/-! # Graded pullback and relative projective quadruple comparisons -/

@[expose] public section

open CategoryTheory CategoryTheory.MonoidalCategory AlgebraicGeometry
open AlgebraicGeometry.AlgebraicSpace Opposite
open SheafOfModules.RingedSite

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.RelativeProj

/-- Concrete data identifying unlifted homogeneous pieces of a graded algebra sheaf with the
module pullback of another family, including the unit and multiplication. This is the
algebraic-space witness that `𝒜'` models `g^* 𝒜`. -/
structure AlgebraPullback {S : Scheme.{u}} {X X' : AlgebraicSpace S} (g : X' ⟶ X)
    {𝒜} (deg : DegreePieces 𝒜) {𝒜'} (deg' : DegreePieces 𝒜') where
  /-- Degreewise identification of unlifted pieces with the pullback of `deg`. -/
  degreeIso : ∀ n : ℕ, (Modules.pullback g).obj (deg.obj n) ≅ deg'.obj n
  /-- The pullback identifications preserve the degree-zero unit. -/
  map_one :
    Modules.structureModulePullbackInv g ≫
        (Modules.pullback g).map (degreeZeroUnit deg) ≫ (degreeIso 0).hom =
      degreeZeroUnit deg'
  /-- The pullback identifications preserve homogeneous multiplication. -/
  map_mul : ∀ i j : ℕ,
    pullbackTensorLax g (deg.obj i) (deg.obj j) ≫
        (Modules.pullback g).map (deg.mul i j) ≫ (degreeIso (i + j)).hom =
      tensorHom (degreeIso i).hom (degreeIso j).hom ≫ deg'.mul i j

namespace AlgebraPullback

variable {S : Scheme.{u}} {X X' : AlgebraicSpace S} {g : X' ⟶ X}
variable {𝒜} {deg : DegreePieces 𝒜} {𝒜'} {deg' : DegreePieces 𝒜'}

/-- Construct genuine graded-algebra pullback data from degreewise isomorphisms
and their unit and multiplication compatibility. -/
def of (degreeIso : ∀ n : ℕ, (Modules.pullback g).obj (deg.obj n) ≅ deg'.obj n)
    (map_one :
      Modules.structureModulePullbackInv g ≫
          (Modules.pullback g).map (degreeZeroUnit deg) ≫ (degreeIso 0).hom =
        degreeZeroUnit deg')
    (map_mul : ∀ i j : ℕ,
      pullbackTensorLax g (deg.obj i) (deg.obj j) ≫
          (Modules.pullback g).map (deg.mul i j) ≫ (degreeIso (i + j)).hom =
        tensorHom (degreeIso i).hom (degreeIso j).hom ≫ deg'.mul i j) :
    AlgebraPullback g deg deg' where
  degreeIso := degreeIso
  map_one := map_one
  map_mul := map_mul

/-- The unit and multiplication of `deg` transport to those of `deg'` along the degreewise
pullback identifications. -/
theorem spec (h : AlgebraPullback g deg deg') :
    (Modules.structureModulePullbackInv g ≫
          (Modules.pullback g).map (degreeZeroUnit deg) ≫ (h.degreeIso 0).hom =
        degreeZeroUnit deg') ∧
      ∀ i j : ℕ,
        pullbackTensorLax g (deg.obj i) (deg.obj j) ≫
            (Modules.pullback g).map (deg.mul i j) ≫ (h.degreeIso (i + j)).hom =
          tensorHom (h.degreeIso i).hom (h.degreeIso j).hom ≫ deg'.mul i j :=
  ⟨h.map_one, h.map_mul⟩

/-- Successive pullbacks along `f'` and `g` identify with pullback along `f' ≫ g` on a
homogeneous piece. -/
def pullbackCompDegreeIso {T : Over S} (f' : ofOver T ⟶ X') (n : ℕ) :
    (Modules.pullback (f' ≫ g)).obj (deg.obj n) ≅
      (Modules.pullback f').obj ((Modules.pullback g).obj (deg.obj n)) :=
  (Modules.pullbackCompIso f' g).symm.app (deg.obj n)


/-- The homogeneous map `ψ` of a quadruple for `g^* 𝒜`, transported first along the
composite-pullback identification `(g ∘ f')^* 𝒜^{(n d)} ≅ f'^* g^* 𝒜^{(n d)}` and then along
`degreeIso`. -/
def transportedPsi (hAlg : AlgebraPullback g deg deg') {T : Over S}
    (q' : Quadruple 𝒜' deg' T) (n : ℕ) :
    (Modules.pullback (q'.morphism ≫ g)).obj (deg.obj (n * q'.degree)) ⟶
      tensorPowerUnit q'.lineBundle n :=
  (pullbackCompDegreeIso q'.morphism (n * q'.degree)).hom ≫
    (Modules.pullback q'.morphism).map (hAlg.degreeIso (n * q'.degree)).hom ≫
      q'.psi n

/-- `transportedPsi` is composite-pullback comparison, then `degreeIso`, then `ψ'`. -/
theorem transportedPsi_eq (hAlg : AlgebraPullback g deg deg') {T : Over S}
    (q' : Quadruple 𝒜' deg' T) (n : ℕ) :
    hAlg.transportedPsi q' n =
      (pullbackCompDegreeIso q'.morphism (n * q'.degree)).hom ≫
        (Modules.pullback q'.morphism).map (hAlg.degreeIso (n * q'.degree)).hom ≫
          q'.psi n :=
  sorry

/-- The forward quadruple `(d', g ∘ f', ℒ', ψ)` of a quadruple for `g^* 𝒜`. -/
def forwardQuadruple (hAlg : AlgebraPullback g deg deg') {T : Over S}
    (q' : Quadruple 𝒜' deg' T) : Quadruple 𝒜 deg T :=
  { degree := q'.degree
    positive := q'.positive
    morphism := q'.morphism ≫ g
    lineBundle := q'.lineBundle
    lineBundle_invertible := q'.lineBundle_invertible
    psi := hAlg.transportedPsi q'
    psi_map_one := sorry
    psi_map_mul := sorry
    degreeOneMap := hAlg.transportedPsi q' 1
    degreeOneMap_spec := sorry
    degreeOne_surjective := sorry }

/-- The image quadruple has degree `d'`, structure morphism `f' ≫ g`, and the same line
bundle. -/
theorem forwardQuadruple_spec (hAlg : AlgebraPullback g deg deg') {T : Over S}
    (q' : Quadruple 𝒜' deg' T) :
    (hAlg.forwardQuadruple q').degree = q'.degree ∧
      (hAlg.forwardQuadruple q').morphism = q'.morphism ≫ g ∧
      (hAlg.forwardQuadruple q').lineBundle = q'.lineBundle :=
  sorry

/-- Inverse transport of `ψ` along `f' ≫ g = f`, using the supplied equality `hf`. -/
def transportedPsiInv (hAlg : AlgebraPullback g deg deg') {T : Over S}
    (f' : ofOver T ⟶ X') (q : Quadruple 𝒜 deg T)
    (hf : f' ≫ g = q.morphism) (n : ℕ) :
    (Modules.pullback f').obj (deg'.obj (n * q.degree)) ⟶
      tensorPowerUnit q.lineBundle n :=
  (Modules.pullback f').map (hAlg.degreeIso (n * q.degree)).inv ≫
    (pullbackCompDegreeIso f' (n * q.degree)).inv ≫
      eqToHom (congrArg (fun φ ↦ (Modules.pullback φ).obj (deg.obj (n * q.degree))) hf) ≫
        q.psi n

/-- `transportedPsiInv` is `degreeIso.inv`, then inverse composite-pullback comparison,
then `eqToHom hf`, then `ψ`. -/
theorem transportedPsiInv_eq (hAlg : AlgebraPullback g deg deg') {T : Over S}
    (f' : ofOver T ⟶ X') (q : Quadruple 𝒜 deg T)
    (hf : f' ≫ g = q.morphism) (n : ℕ) :
    hAlg.transportedPsiInv f' q hf n =
      (Modules.pullback f').map (hAlg.degreeIso (n * q.degree)).inv ≫
        (pullbackCompDegreeIso f' (n * q.degree)).inv ≫
          eqToHom
              (congrArg (fun φ ↦ (Modules.pullback φ).obj (deg.obj (n * q.degree))) hf) ≫
            q.psi n :=
  sorry

/-- The inverse quadruple `(d, f', ℒ, ψ)` of `(f', (d, f, ℒ, ψ))`. -/
def inverseQuadruple (hAlg : AlgebraPullback g deg deg') {T : Over S}
    (f' : ofOver T ⟶ X') (q : Quadruple 𝒜 deg T)
    (hf : f' ≫ g = q.morphism) : Quadruple 𝒜' deg' T :=
  { degree := q.degree
    positive := q.positive
    morphism := f'
    lineBundle := q.lineBundle
    lineBundle_invertible := q.lineBundle_invertible
    psi := hAlg.transportedPsiInv f' q hf
    psi_map_one := sorry
    psi_map_mul := sorry
    degreeOneMap := hAlg.transportedPsiInv f' q hf 1
    degreeOneMap_spec := sorry
    degreeOne_surjective := sorry }

/-- The preimage quadruple has degree `d`, structure morphism `f'`, and the same line
bundle. -/
theorem inverseQuadruple_spec (hAlg : AlgebraPullback g deg deg') {T : Over S}
    (f' : ofOver T ⟶ X') (q : Quadruple 𝒜 deg T)
    (hf : f' ≫ g = q.morphism) :
    (hAlg.inverseQuadruple f' q hf).degree = q.degree ∧
      (hAlg.inverseQuadruple f' q hf).morphism = f' ∧
      (hAlg.inverseQuadruple f' q hf).lineBundle = q.lineBundle :=
  sorry

end AlgebraPullback

/-- The fibre product `X' ×_X relative Proj of 𝒜 over X`. -/
def fibreProduct {S : Scheme.{u}} {X X' : AlgebraicSpace S} (g : X' ⟶ X)
    {𝒜} {deg : DegreePieces 𝒜} {F : ProjFunctor X 𝒜}
    (hF : F.IsAssociatedToQuadruples deg) : AlgebraicSpace S :=
  ReasLibPullback.pullbackOver g (toAlgebraicSpace_hom F hF) X.isSheaf X.representableDiagonal


/-- The projection `X' ×_X P ⟶ X'`. -/
def fibreProduct_fst {S : Scheme.{u}} {X X' : AlgebraicSpace S} (g : X' ⟶ X)
    {𝒜} {deg : DegreePieces 𝒜} {F : ProjFunctor X 𝒜}
    (hF : F.IsAssociatedToQuadruples deg) :
    fibreProduct g hF ⟶ X' :=
  ReasLibPullback.pullbackOverFst g (toAlgebraicSpace_hom F hF) X.isSheaf X.representableDiagonal

/-- The projection `X' ×_X P ⟶ P`. -/
def fibreProduct_snd {S : Scheme.{u}} {X X' : AlgebraicSpace S} (g : X' ⟶ X)
    {𝒜} {deg : DegreePieces 𝒜} {F : ProjFunctor X 𝒜}
    (hF : F.IsAssociatedToQuadruples deg) :
    fibreProduct g hF ⟶ toAlgebraicSpace F hF :=
  ReasLibPullback.pullbackOverSnd g (toAlgebraicSpace_hom F hF) X.isSheaf X.representableDiagonal



/-- The morphism `ofOver T ⟶ X` associated to a `T`-point of an algebraic space. -/
def pointHom {S : Scheme.{u}} {X : AlgebraicSpace S} {T : Over S}
    (t : X.functorOfPoints.obj (op T)) : ofOver T ⟶ X :=
  yonedaEquiv.symm t


/-- The comparison isomorphism `r` acts by the forward and inverse quadruple formulas on quasi-compact
test schemes. -/
def ActsByQuadrupleFormula {S : Scheme.{u}} {X X' : AlgebraicSpace S} (g : X' ⟶ X)
    {𝒜} {𝒜'}
    {deg : DegreePieces 𝒜} {deg' : DegreePieces 𝒜'}
    (hAlg : AlgebraPullback g deg deg')
    {F : ProjFunctor X 𝒜} (hF : F.IsAssociatedToQuadruples deg)
    {F' : ProjFunctor X' 𝒜'} (hF' : F'.IsAssociatedToQuadruples deg')
    (r : toAlgebraicSpace F' hF' ≅ fibreProduct g hF) : Prop :=
  (∀ (T : Over S) [CompactSpace T.left]
      (x' : F'.toFunctor.obj (op T)) (q' : Quadruple 𝒜' deg' T),
      hF'.associated T x' q' →
        (fibreProduct_fst g hF).app (op T)
              (r.hom.app (op T) x') =
            q'.morphism.app (op T) (𝟙 T) ∧
          ∃ x : F.toFunctor.obj (op T),
            hF.associated T x (hAlg.forwardQuadruple q') ∧
              (fibreProduct_snd g hF).app (op T)
                  (r.hom.app (op T) x') =
                x) ∧
    ∀ (T : Over S) [CompactSpace T.left]
      (y : (fibreProduct g hF).functorOfPoints.obj (op T))
      (x : F.toFunctor.obj (op T)) (q : Quadruple 𝒜 deg T),
      hF.associated T x q →
        (fibreProduct_snd g hF).app (op T) y = x →
          ∃ (x' : F'.toFunctor.obj (op T)) (f' : ofOver T ⟶ X')
            (hf : f' ≫ g = q.morphism),
            f' = pointHom
                ((fibreProduct_fst g hF).app (op T) y) ∧
              hF'.associated T x' (hAlg.inverseQuadruple f' q hf) ∧
                r.inv.app (op T) y = x'

end AlgebraicGeometry.AlgebraicSpace.RelativeProj
