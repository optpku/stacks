module

public import ReasLib.AlgebraicGeometry.Scheme.Etale.Representability
import StacksCheckRecall

open CategoryTheory
open AlgebraicGeometry

@[expose] public section

universe u

/- Remark 59.56.4: every sheaf on the chosen small étale site of a field spectrum
is represented by an ambient étale scheme. The representing scheme need not be
an object of the chosen small site, so this is not necessarily representability
in the sense of Sites, Definition 7.12.3. -/
@[stacks 04JL] #check
  (AlgebraicGeometry.Scheme.Etale.sheaf_isRepresentableByEtaleScheme :
    ∀ {C : Type u} [Category.{u} C] (K : Type u) [Field K]
      (J : GrothendieckTopology C) (ι : C ⥤ (Spec (.of K)).Etale)
      [ι.Full] [ι.Faithful] [ι.IsDenseSubsite J (Spec (.of K)).smallEtaleTopology]
      (F : Sheaf J (Type u)),
      ∃ X : (Spec (.of K)).Etale, Nonempty (F.obj ≅ (ι.op ⋙ CategoryTheory.yoneda.obj X)))

/- The chosen small site does not represent all of its set-valued sheaves by
its own objects: the size obstruction is unconditional. -/
#check
  (AlgebraicGeometry.Scheme.Etale.exists_not_isRepresentable_on_smallSite :
    ∀ {C : Type u} [Category.{u} C] (K : Type u) [Field K]
      (J : GrothendieckTopology C) (ι : C ⥤ (Spec (.of K)).Etale)
      [ι.Full] [ι.Faithful] [ι.IsDenseSubsite J (Spec (.of K)).smallEtaleTopology],
      ∃ F : Sheaf J (Type u), ¬ F.obj.IsRepresentable)
