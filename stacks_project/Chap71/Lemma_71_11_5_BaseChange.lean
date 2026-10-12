/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.Yoneda
public import stacks_project.Chap65.Lemma_65_7_2_Pullback
public import stacks_project.Chap71.Lemma_71_11_2_Functor

/-!
# Base change for relative projective spectra of algebraic spaces

A morphism of algebraic spaces and relative `Proj` functors associated to
quadruples determine a comparison isomorphism `r` with the fibre product, together
with a corresponding graded-algebra comparison of twist families along `r ≫ pr₂`.
-/

@[expose]
public section

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

/-- `pullbackCompDegreeIso` is the inverse of `Modules.pullbackCompIso` on a homogeneous
piece. -/
theorem pullbackCompDegreeIso_eq {T : Over S} (f' : ofOver T ⟶ X') (n : ℕ) :
    pullbackCompDegreeIso f' n =
      (Modules.pullbackCompIso f' g).symm.app (deg.obj n) :=
  sorry

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

/-- The Stacks image quadruple `(d', g ∘ f', ℒ', ψ)` of a quadruple for `g^* 𝒜`. -/
def forwardQuadruple (hAlg : AlgebraPullback g deg deg') {T : Over S}
    (q' : Quadruple 𝒜' deg' T) : Quadruple 𝒜 deg T :=
  Quadruple.of q'.degree q'.positive (q'.morphism ≫ g) q'.lineBundle
    q'.lineBundle_invertible (hAlg.transportedPsi q') sorry sorry
    (hAlg.transportedPsi q' 1) sorry sorry

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

/-- The Stacks preimage quadruple `(d, f', ℒ, ψ)` of `(f', (d, f, ℒ, ψ))`. -/
def inverseQuadruple (hAlg : AlgebraPullback g deg deg') {T : Over S}
    (f' : ofOver T ⟶ X') (q : Quadruple 𝒜 deg T)
    (hf : f' ≫ g = q.morphism) : Quadruple 𝒜' deg' T :=
  Quadruple.of q.degree q.positive f' q.lineBundle q.lineBundle_invertible
    (hAlg.transportedPsiInv f' q hf) sorry sorry
    (hAlg.transportedPsiInv f' q hf 1) sorry sorry

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

/-- The fibre product `X' ×_X underline{Proj}_X(𝒜)`. -/
def fibreProduct {S : Scheme.{u}} {X X' : AlgebraicSpace S} (g : X' ⟶ X)
    {𝒜} {deg : DegreePieces 𝒜} {F : ProjFunctor X 𝒜}
    (hF : F.IsAssociatedToQuadruples deg) : AlgebraicSpace S :=
  pullbackOver g (toAlgebraicSpace_hom F hF) X.isSheaf X.representableDiagonal

/-- `fibreProduct g hF` is the sheaf fibre product of `g` and `π`. -/
theorem fibreProduct_eq {S : Scheme.{u}} {X X' : AlgebraicSpace S} (g : X' ⟶ X)
    {𝒜} {deg : DegreePieces 𝒜} {F : ProjFunctor X 𝒜}
    (hF : F.IsAssociatedToQuadruples deg) :
    fibreProduct g hF =
      pullbackOver g (toAlgebraicSpace_hom F hF) X.isSheaf X.representableDiagonal :=
  sorry

/-- The projection `X' ×_X P ⟶ X'`. -/
def fibreProduct_fst {S : Scheme.{u}} {X X' : AlgebraicSpace S} (g : X' ⟶ X)
    {𝒜} {deg : DegreePieces 𝒜} {F : ProjFunctor X 𝒜}
    (hF : F.IsAssociatedToQuadruples deg) :
    fibreProduct g hF ⟶ X' :=
  pullbackOverFst g (toAlgebraicSpace_hom F hF) X.isSheaf X.representableDiagonal

/-- The projection `X' ×_X P ⟶ P`. -/
def fibreProduct_snd {S : Scheme.{u}} {X X' : AlgebraicSpace S} (g : X' ⟶ X)
    {𝒜} {deg : DegreePieces 𝒜} {F : ProjFunctor X 𝒜}
    (hF : F.IsAssociatedToQuadruples deg) :
    fibreProduct g hF ⟶ toAlgebraicSpace F hF :=
  pullbackOverSnd g (toAlgebraicSpace_hom F hF) X.isSheaf X.representableDiagonal

/-- `fibreProduct_fst` is the first projection of the sheaf fibre product. -/
theorem fibreProduct_fst_eq {S : Scheme.{u}} {X X' : AlgebraicSpace S} (g : X' ⟶ X)
    {𝒜} {deg : DegreePieces 𝒜} {F : ProjFunctor X 𝒜}
    (hF : F.IsAssociatedToQuadruples deg) :
    fibreProduct_fst g hF =
      pullbackOverFst g (toAlgebraicSpace_hom F hF) X.isSheaf X.representableDiagonal :=
  sorry

/-- `fibreProduct_snd` is the second projection of the sheaf fibre product. -/
theorem fibreProduct_snd_eq {S : Scheme.{u}} {X X' : AlgebraicSpace S} (g : X' ⟶ X)
    {𝒜} {deg : DegreePieces 𝒜} {F : ProjFunctor X 𝒜}
    (hF : F.IsAssociatedToQuadruples deg) :
    fibreProduct_snd g hF =
      pullbackOverSnd g (toAlgebraicSpace_hom F hF) X.isSheaf X.representableDiagonal :=
  sorry

/-- The unlifted Serre twist family `⊕_d 𝒪_P(d)` on a fixed algebraic space. -/
structure TwistFamily {S : Scheme.{u}} (P : AlgebraicSpace S) where
  /-- The `ℤ`-graded algebra sheaf whose degree-`n` piece is `𝒪_P(n)`. -/
  algebra : GradedAlgebraSheaf.{u + 1, u} (commStructureSheafLift P)
  /-- The unlifted family of twist modules `𝒪_P(n)`. -/
  obj : ℤ → P.Modules
  /-- Universe lift identifies `𝒪_P(n)` with the degree-`n` piece of the twist algebra. -/
  iso : ∀ n : ℤ, Modules.liftModule (obj n) ≅ algebra.obj n
  /-- Unlifted multiplication of twists. -/
  mul : ∀ n m : ℤ, obj n ⊗ obj m ⟶ obj (n + m)
  /-- The unlifted degree-zero unit. -/
  unit : SheafOfModules.unit (structureSheaf P) ⟶ obj 0
  /-- The unit is the actual unit of the displayed graded algebra after universe transport. -/
  unit_spec :
    (Modules.liftedUnitIso P).inv ≫ Modules.liftModuleMap unit ≫ (iso 0).hom =
      gradedOneHom algebra
  /-- Multiplication agrees with the displayed graded algebra after universe transport. -/
  mul_spec : ∀ n m : ℤ,
    liftModuleTensorHom (obj n) (obj m) ≫ Modules.liftModuleMap (mul n m) =
      ((iso n).hom ⊗ₘ (iso m).hom) ≫ GradedAlgebraSheaf.mulHom algebra n m ≫
        (iso (n + m)).inv

namespace TwistFamily

variable {S : Scheme.{u}} {P : AlgebraicSpace S}

/-- Construct a twist family from its algebra, unlifted modules, comparison isomorphisms,
multiplication, and unit. -/
def of (algebra : GradedAlgebraSheaf.{u + 1, u} (commStructureSheafLift P))
    (obj : ℤ → P.Modules)
    (iso : ∀ n : ℤ, Modules.liftModule (obj n) ≅ algebra.obj n)
    (mul : ∀ n m : ℤ, obj n ⊗ obj m ⟶ obj (n + m))
    (unit : SheafOfModules.unit (structureSheaf P) ⟶ obj 0)
    (unit_spec :
      (Modules.liftedUnitIso P).inv ≫ Modules.liftModuleMap unit ≫ (iso 0).hom =
        gradedOneHom algebra)
    (mul_spec : ∀ n m : ℤ,
      liftModuleTensorHom (obj n) (obj m) ≫ Modules.liftModuleMap (mul n m) =
        ((iso n).hom ⊗ₘ (iso m).hom) ≫ GradedAlgebraSheaf.mulHom algebra n m ≫
          (iso (n + m)).inv) :
    TwistFamily P where
  algebra := algebra
  obj := obj
  iso := iso
  mul := mul
  unit := unit
  unit_spec := unit_spec
  mul_spec := mul_spec

/-- Universe lift of `A.obj n` is the degree-`n` piece of `A.algebra`. -/
def iso_spec (A : TwistFamily P) (n : ℤ) :
    Modules.liftModule (A.obj n) ≅ A.algebra.obj n :=
  A.iso n

/-- `iso_spec A n` is the stored comparison isomorphism. -/
theorem iso_spec_eq (A : TwistFamily P) (n : ℤ) :
    iso_spec A n = A.iso n :=
  sorry

end TwistFamily

/-- A graded-algebra comparison along a morphism of algebraic spaces: degreewise module maps
together with unit and multiplication preservation. -/
structure GradedAlgebraComparison {S : Scheme.{u}} {Y Y' : AlgebraicSpace S} (f : Y' ⟶ Y)
    (A : TwistFamily Y) (A' : TwistFamily Y') where
  /-- The degreewise comparison from the pullback of `A` to `A'`. -/
  degreeMap : ∀ n : ℤ, (Modules.pullback f).obj (A.obj n) ⟶ A'.obj n
  /-- The degree-zero unit is preserved. -/
  map_one :
    Modules.structureModulePullbackInv f ≫
        (Modules.pullback f).map A.unit ≫ degreeMap 0 =
      A'.unit
  /-- Homogeneous multiplication is preserved. -/
  map_mul :
    ∀ n m : ℤ,
      pullbackTensorLax f (A.obj n) (A.obj m) ≫
          (Modules.pullback f).map (A.mul n m) ≫ degreeMap (n + m) =
        tensorHom (degreeMap n) (degreeMap m) ≫ A'.mul n m

namespace GradedAlgebraComparison

variable {S : Scheme.{u}} {Y Y' : AlgebraicSpace S} {f : Y' ⟶ Y}
variable {A : TwistFamily Y} {A' : TwistFamily Y'}

/-- Construct a graded-algebra comparison from its degree maps and algebra laws. -/
def of (degreeMap : ∀ n : ℤ, (Modules.pullback f).obj (A.obj n) ⟶ A'.obj n)
    (map_one :
      Modules.structureModulePullbackInv f ≫
          (Modules.pullback f).map A.unit ≫ degreeMap 0 = A'.unit)
    (map_mul : ∀ n m : ℤ,
      pullbackTensorLax f (A.obj n) (A.obj m) ≫
          (Modules.pullback f).map (A.mul n m) ≫ degreeMap (n + m) =
        tensorHom (degreeMap n) (degreeMap m) ≫ A'.mul n m) :
    GradedAlgebraComparison f A A' where
  degreeMap := degreeMap
  map_one := map_one
  map_mul := map_mul

/-- The unit and multiplication of `A` transport to those of `A'` along the degreewise
maps. -/
theorem spec (θ : GradedAlgebraComparison f A A') :
    (Modules.structureModulePullbackInv f ≫
          (Modules.pullback f).map A.unit ≫ θ.degreeMap 0 =
        A'.unit) ∧
      ∀ n m : ℤ,
        pullbackTensorLax f (A.obj n) (A.obj m) ≫
            (Modules.pullback f).map (A.mul n m) ≫ θ.degreeMap (n + m) =
          tensorHom (θ.degreeMap n) (θ.degreeMap m) ≫ A'.mul n m :=
  sorry

end GradedAlgebraComparison

/-- The morphism `ofOver T ⟶ X` associated to a `T`-point of an algebraic space. -/
def pointHom {S : Scheme.{u}} {X : AlgebraicSpace S} {T : Over S}
    (t : X.functorOfPoints.obj (op T)) : ofOver T ⟶ X :=
  yonedaEquiv.symm t

/-- `pointHom t` is Yoneda inversion of the `T`-point `t`. -/
theorem pointHom_eq {S : Scheme.{u}} {X : AlgebraicSpace S} {T : Over S}
    (t : X.functorOfPoints.obj (op T)) :
    pointHom t = yonedaEquiv.symm t :=
  sorry

/-- The comparison isomorphism `r` acts by the Stacks quadruple formula on quasi-compact
test schemes. -/
def ActsByStacksFormula {S : Scheme.{u}} {X X' : AlgebraicSpace S} (g : X' ⟶ X)
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

/-- `ActsByStacksFormula` is the Stacks image formula together with the inverse formula. -/
theorem actsByStacksFormula_iff {S : Scheme.{u}} {X X' : AlgebraicSpace S} (g : X' ⟶ X)
    {𝒜} {𝒜'}
    {deg : DegreePieces 𝒜} {deg' : DegreePieces 𝒜'}
    (hAlg : AlgebraPullback g deg deg')
    {F : ProjFunctor X 𝒜} (hF : F.IsAssociatedToQuadruples deg)
    {F' : ProjFunctor X' 𝒜'} (hF' : F'.IsAssociatedToQuadruples deg')
    (r : toAlgebraicSpace F' hF' ≅ fibreProduct g hF) :
    ActsByStacksFormula g hAlg hF hF' r ↔
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
                    r.inv.app (op T) y = x' :=
  sorry

/-- Comparison data for relative `Proj` of algebraic spaces along a base change `g : X' ⟶ X`:
an isomorphism `r : P' ≅ X' ×_X P` over `X'`, together with the corresponding graded twist
comparison along `r ≫ pr₂`. -/
structure BaseChange {S : Scheme.{u}} {X X' : AlgebraicSpace S} (g : X' ⟶ X)
    {𝒜} {𝒜'}
    {deg : DegreePieces 𝒜} {deg' : DegreePieces 𝒜'}
    (algebraPullback : AlgebraPullback g deg deg')
    {F : ProjFunctor X 𝒜} (hF : F.IsAssociatedToQuadruples deg)
    {F' : ProjFunctor X' 𝒜'} (hF' : F'.IsAssociatedToQuadruples deg')
    (twistP : TwistFamily (toAlgebraicSpace F hF))
    (twistP' : TwistFamily (toAlgebraicSpace F' hF')) where
  /-- The comparison isomorphism `r : P' ≅ X' ×_X P`. -/
  iso : toAlgebraicSpace F' hF' ≅ fibreProduct g hF
  /-- `r` is a morphism of algebraic spaces over `X'`. -/
  iso_fst :
    iso.hom ≫ fibreProduct_fst g hF = toAlgebraicSpace_hom F' hF'
  /-- The corresponding graded twist comparison along `r ≫ pr₂`. -/
  theta :
    GradedAlgebraComparison (iso.hom ≫ fibreProduct_snd g hF)
      twistP twistP'

namespace BaseChange

variable {S : Scheme.{u}} {X X' : AlgebraicSpace S} {g : X' ⟶ X}
variable {𝒜} {deg : DegreePieces 𝒜} {𝒜'} {deg' : DegreePieces 𝒜'}
variable {algebraPullback : AlgebraPullback g deg deg'}
variable {F : ProjFunctor X 𝒜} {hF : F.IsAssociatedToQuadruples deg}
variable {F' : ProjFunctor X' 𝒜'} {hF' : F'.IsAssociatedToQuadruples deg'}
variable {twistP : TwistFamily (toAlgebraicSpace F hF)}
variable {twistP' : TwistFamily (toAlgebraicSpace F' hF')}

/-- Construct relative-Proj base-change data from a space isomorphism over `X'` and a
graded twist comparison along `r ≫ pr₂`. This does not assert the Stacks quadruple
formula, which holds only for the canonical `r`. -/
def of (iso : toAlgebraicSpace F' hF' ≅ fibreProduct g hF)
    (iso_fst :
      iso.hom ≫ fibreProduct_fst g hF = toAlgebraicSpace_hom F' hF')
    (theta :
      GradedAlgebraComparison (iso.hom ≫ fibreProduct_snd g hF)
        twistP twistP') :
    BaseChange g algebraPullback hF hF' twistP twistP' where
  iso := iso
  iso_fst := iso_fst
  theta := theta

/-- A base-change comparison is a morphism over `X'`. -/
theorem spec (bc : BaseChange g algebraPullback hF hF' twistP twistP') :
    bc.iso.hom ≫ fibreProduct_fst g hF =
      toAlgebraicSpace_hom F' hF' :=
  sorry

/-- `iso_fst` is the stored triangle identity over `X'`. -/
theorem iso_fst_eq (bc : BaseChange g algebraPullback hF hF' twistP twistP') :
    bc.iso.hom ≫ fibreProduct_fst g hF =
      toAlgebraicSpace_hom F' hF' :=
  sorry

/-- The degree-zero unit and homogeneous multiplication are preserved by the twist
comparison of `bc`. -/
theorem theta_spec (bc : BaseChange g algebraPullback hF hF' twistP twistP') :
    (Modules.structureModulePullbackInv
          (bc.iso.hom ≫ fibreProduct_snd g hF) ≫
        (Modules.pullback
            (bc.iso.hom ≫ fibreProduct_snd g hF)).map
          twistP.unit ≫
        bc.theta.degreeMap 0 =
      twistP'.unit) ∧
      ∀ n m : ℤ,
        pullbackTensorLax (bc.iso.hom ≫ fibreProduct_snd g hF)
            (twistP.obj n) (twistP.obj m) ≫
          (Modules.pullback
              (bc.iso.hom ≫ fibreProduct_snd g hF)).map
            (twistP.mul n m) ≫
          bc.theta.degreeMap (n + m) =
        tensorHom (bc.theta.degreeMap n) (bc.theta.degreeMap m) ≫ twistP'.mul n m :=
  sorry

end BaseChange

end AlgebraicGeometry.AlgebraicSpace.RelativeProj
