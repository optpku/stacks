module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.Cohomology.RelativeMayerVietoris
import StacksCheckRecall

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

noncomputable section

universe u

variable (X Y : Scheme.{u}) (f : X ⟶ Y) (U V : X.Opens) (hUV : U ⊔ V = ⊤)
variable [HasWeakSheafify X.smallEtaleTopology (Type u)]
variable [HasSheafify X.smallEtaleTopology AddCommGrpCat.{u}]
variable [HasSheafify Y.smallEtaleTopology AddCommGrpCat.{u}]
variable [HasExt.{u} (Sheaf X.smallEtaleTopology AddCommGrpCat.{u})]

/- Lemma 59.50.2 (Relative Mayer-Vietoris) (1): the relative long exact sequence
on `Yₑₜ` is exact, including its augmented degree-zero window, and its degree-zero
direct-image functor is naturally isomorphic to ordinary `f_*`. -/
@[stacks 0EYK] #check
  (EtaleRelativeMayerVietoris.etaleRelativeMayerVietorisExact X Y f U V hUV :
    IsIsomorphic (EtaleRelativeMayerVietoris.relativeHigherDirectImage f 0)
        ((Scheme.smallEtalePullback f).sheafPushforwardContinuous
          AddCommGrpCat.{u} Y.smallEtaleTopology X.smallEtaleTopology) ∧
      ∀ F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u},
        ((EtaleRelativeMayerVietoris.sequence f U V hUV 0 F).zeroPrecomp 1).Exact ∧
          ∀ n : ℕ, (EtaleRelativeMayerVietoris.sequence f U V hUV n F).Exact)

variable (n : ℕ) {F G : Sheaf X.smallEtaleTopology AddCommGrpCat.{u}} (φ : F ⟶ G)

/- Lemma 59.50.2 (Relative Mayer-Vietoris) (2): the relative Mayer–Vietoris
windows are functorial in the abelian coefficient sheaf. -/
@[stacks 0EYK] #check
  (EtaleRelativeMayerVietoris.etaleRelativeMayerVietorisFunctorial X Y f U V hUV n φ :
    (EtaleRelativeMayerVietoris.sequenceFunctor f U V hUV n).obj F =
        EtaleRelativeMayerVietoris.sequence f U V hUV n F ∧
      (EtaleRelativeMayerVietoris.sequenceFunctor f U V hUV n).map φ =
        EtaleRelativeMayerVietoris.sequenceMap f U V hUV φ n)
