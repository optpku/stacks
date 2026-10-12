/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.LocallyRingedSpace.Module.Ideal.Regularity.StalkBasis
import StacksCheckRecall

@[expose] public section

universe u

/- Lemma 31.20.5 (1): a residue-field basis of the stalk of a quasi-regular ideal sheaf lifts
on a neighborhood to a quasi-regular family with the prescribed germs that generates the
restricted ideal sheaf. -/
@[stacks 067N] #check
  (AlgebraicGeometry.LocallyRingedSpace.exists_quasiRegularSequence_of_stalk_basis :
    ∀ {X : AlgebraicGeometry.LocallyRingedSpace.{u}}
      (I : AlgebraicGeometry.LocallyRingedSpace.IdealSubobject X)
      (hI : AlgebraicGeometry.RingedSpace.IsQuasiRegularIdealSheaf I)
      (x : X) {r : ℕ}
      (f : Fin r → AlgebraicGeometry.RingedSpace.idealSheafStalkIdeal I x)
      (hf_basis : ∃ b : Module.Basis (Fin r)
          ((X.presheaf.stalk x) ⧸ IsLocalRing.maximalIdeal (X.presheaf.stalk x))
          (AlgebraicGeometry.LocallyRingedSpace.idealStalkFiber I x),
        ∀ i, AlgebraicGeometry.LocallyRingedSpace.idealStalkFiberMk I x (f i) = b i),
      ∃ (U : TopologicalSpace.Opens X) (hxU : x ∈ U)
        (g : Fin r → I.toModule.val.obj (Opposite.op U)),
        (∀ i,
          (AlgebraicGeometry.RingedSpace.idealSheafStalkToRing I x).hom
            (TopCat.Presheaf.germ I.toModule.val.presheaf U x hxU (g i)) = f i) ∧
          AlgebraicGeometry.RingedSpace.IsGeneratedByIdealSectionFamilyOn I U g ∧
          AlgebraicGeometry.RingedSpace.SectionSequence.IsQuasiRegular
            (fun i ↦ AlgebraicGeometry.RingedSpace.idealSectionToRingSection I U (g i)))

/- Lemma 31.20.5 (2): a residue-field basis of the stalk of an `H₁`-regular ideal sheaf lifts
on a neighborhood to an `H₁`-regular family with the prescribed germs that generates the
restricted ideal sheaf. -/
@[stacks 067N] #check
  (AlgebraicGeometry.LocallyRingedSpace.exists_h1RegularSequence_of_stalk_basis :
    ∀ {X : AlgebraicGeometry.LocallyRingedSpace.{u}}
      (I : AlgebraicGeometry.LocallyRingedSpace.IdealSubobject X)
      (hI : AlgebraicGeometry.RingedSpace.IsH1RegularIdealSheaf I)
      (x : X) {r : ℕ}
      (f : Fin r → AlgebraicGeometry.RingedSpace.idealSheafStalkIdeal I x)
      (hf_basis : ∃ b : Module.Basis (Fin r)
          ((X.presheaf.stalk x) ⧸ IsLocalRing.maximalIdeal (X.presheaf.stalk x))
          (AlgebraicGeometry.LocallyRingedSpace.idealStalkFiber I x),
        ∀ i, AlgebraicGeometry.LocallyRingedSpace.idealStalkFiberMk I x (f i) = b i),
      ∃ (U : TopologicalSpace.Opens X) (hxU : x ∈ U)
        (g : Fin r → I.toModule.val.obj (Opposite.op U)),
        (∀ i,
          (AlgebraicGeometry.RingedSpace.idealSheafStalkToRing I x).hom
            (TopCat.Presheaf.germ I.toModule.val.presheaf U x hxU (g i)) = f i) ∧
          AlgebraicGeometry.RingedSpace.IsGeneratedByIdealSectionFamilyOn I U g ∧
          AlgebraicGeometry.RingedSpace.SectionSequence.IsH1Regular
            (fun i ↦ AlgebraicGeometry.RingedSpace.idealSectionToRingSection I U (g i)))

/- Lemma 31.20.5 (3): a residue-field basis of the stalk of a Koszul-regular ideal sheaf lifts
on a neighborhood to a Koszul-regular family with the prescribed germs that generates the
restricted ideal sheaf. -/
@[stacks 067N] #check
  (AlgebraicGeometry.LocallyRingedSpace.exists_koszulRegularSequence_of_stalk_basis :
    ∀ {X : AlgebraicGeometry.LocallyRingedSpace.{u}}
      (I : AlgebraicGeometry.LocallyRingedSpace.IdealSubobject X)
      (hI : AlgebraicGeometry.RingedSpace.IsKoszulRegularIdealSheaf I)
      (x : X) {r : ℕ}
      (f : Fin r → AlgebraicGeometry.RingedSpace.idealSheafStalkIdeal I x)
      (hf_basis : ∃ b : Module.Basis (Fin r)
          ((X.presheaf.stalk x) ⧸ IsLocalRing.maximalIdeal (X.presheaf.stalk x))
          (AlgebraicGeometry.LocallyRingedSpace.idealStalkFiber I x),
        ∀ i, AlgebraicGeometry.LocallyRingedSpace.idealStalkFiberMk I x (f i) = b i),
      ∃ (U : TopologicalSpace.Opens X) (hxU : x ∈ U)
        (g : Fin r → I.toModule.val.obj (Opposite.op U)),
        (∀ i,
          (AlgebraicGeometry.RingedSpace.idealSheafStalkToRing I x).hom
            (TopCat.Presheaf.germ I.toModule.val.presheaf U x hxU (g i)) = f i) ∧
          AlgebraicGeometry.RingedSpace.IsGeneratedByIdealSectionFamilyOn I U g ∧
          AlgebraicGeometry.RingedSpace.SectionSequence.IsKoszulRegular
            (fun i ↦ AlgebraicGeometry.RingedSpace.idealSectionToRingSection I U (g i)))
