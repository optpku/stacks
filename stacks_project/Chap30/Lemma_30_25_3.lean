module

public import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial
public import Mathlib.AlgebraicGeometry.Restrict
public import ReasLib.AlgebraicGeometry.Scheme.CoherentFormalModule.Completion
public import ReasLib.AlgebraicGeometry.Scheme.CoherentFormalModule.MapAnnihilation
public import ReasLib.AlgebraicGeometry.Scheme.IdealSheafData.OpenComplement
public import ReasLib.AlgebraicGeometry.Scheme.Module.Coherent.Proper
public import ReasLib.AlgebraicGeometry.Scheme.Module.Pullback.Coherent

@[expose] public section

open AlgebraicGeometry CategoryTheory Opposite

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Modules

variable {X Y : Scheme.{u}}

/-- The ordinary pushforward of a coherent module along a proper morphism, as a coherent module
on the target. -/
def coherentPushforwardObj [IsLocallyNoetherian Y] (f : X ⟶ Y) [IsProper f]
    (F : RingedSpace.Coh X.toRingedSpace) : RingedSpace.Coh Y.toRingedSpace :=
  ⟨(pushforward f).obj F.obj, @pushforward_obj_isCoherent_of_proper X Y f _ _ F.obj F.property⟩

/-- The underlying module sheaf of `coherentPushforwardObj` is ordinary pushforward. -/
theorem coherentPushforwardObj_obj [IsLocallyNoetherian Y] (f : X ⟶ Y) [IsProper f]
    (F : RingedSpace.Coh X.toRingedSpace) :
    (coherentPushforwardObj f F).obj = (pushforward f).obj F.obj :=
  sorry

end AlgebraicGeometry.Scheme.Modules

namespace AlgebraicGeometry.Scheme.CoherentFormalModules

variable {X Y : Scheme.{u}}

/-- Stage `n` of the stagewise pullback of a coherent formal module along `f`. -/
def pullbackStage [IsLocallyNoetherian X] [IsLocallyNoetherian Y] (f : X ⟶ Y)
    {J : Y.IdealSheafData} (G : CoherentFormalModules Y J) (n : ℕ) :
    RingedSpace.Coh X.toRingedSpace :=
  ⟨(Modules.pullback f).obj (((G.obj).obj (op n)).obj),
    @Modules.pullback_isCoherent X Y _ _ f
      (((G.obj).obj (op n)).obj) ((G.obj).obj (op n)).property⟩

/-- The underlying module of `pullbackStage` is ordinary pullback of the corresponding stage. -/
theorem pullbackStage_obj [IsLocallyNoetherian X] [IsLocallyNoetherian Y] (f : X ⟶ Y)
    {J : Y.IdealSheafData} (G : CoherentFormalModules Y J) (n : ℕ) :
    (pullbackStage f G n).obj = (Modules.pullback f).obj (((G.obj).obj (op n)).obj) :=
  sorry

/-- The stagewise pullback of a coherent formal module along `f`, as an object of
`CoherentFormalModules X (J.comap f)`. -/
def pullbackObj [IsLocallyNoetherian X] [IsLocallyNoetherian Y] (f : X ⟶ Y)
    (J : Y.IdealSheafData) (G : CoherentFormalModules Y J) :
    CoherentFormalModules X (J.comap f) where
  obj :=
    Functor.ofOpSequence fun n ↦
      (ObjectProperty.homMk
        ((Modules.pullback f).map
          (((G.obj).map (homOfLE (Nat.le_add_right n 1)).op).hom)) :
        pullbackStage f G (n + 1) ⟶ pullbackStage f G n)
  property := sorry

/-- Stage `n` of `pullbackObj` is the ordinary module pullback of stage `n`. -/
theorem pullbackObj_stage_obj [IsLocallyNoetherian X] [IsLocallyNoetherian Y]
    (f : X ⟶ Y) (J : Y.IdealSheafData) (G : CoherentFormalModules Y J) (n : ℕ) :
    (((pullbackObj f J G).obj).obj (op n)).obj =
      (Modules.pullback f).obj (((G.obj).obj (op n)).obj) :=
  sorry

/-- Lemma 30.25.3: Let `Y` be a Noetherian scheme, let `J` and `K` be quasi-coherent sheaves of
ideals on `Y`, and let `f : X ⟶ Y` be a proper morphism which is an isomorphism over
`V = K.openComplement`. Set `I = J.comap f`. Let `G` be an object of
`CoherentFormalModules Y J`, let `F` be a coherent `𝒪_X`-module, and let
`β : pullbackObj f J G ≅ (CoherentCompletion.functor I).obj F` be an isomorphism in
`CoherentFormalModules X I`. Then there exists a map
`α : G ⟶ (CoherentCompletion.functor J).obj (Modules.coherentPushforwardObj f F)`
in `CoherentFormalModules Y J` whose kernel and cokernel are annihilated by a power of `K`. -/
@[stacks 088B]
theorem exists_map_to_pushforwardCompletion
    [IsNoetherian X] [IsNoetherian Y]
    (J K : Y.IdealSheafData) (f : X ⟶ Y)
    [IsProper f] [IsIso (f ∣_ K.openComplement)]
    (G : CoherentFormalModules Y J) (F : RingedSpace.Coh X.toRingedSpace)
    (β : pullbackObj f J G ≅ (CoherentCompletion.functor (J.comap f)).obj F) :
    ∃ α : G ⟶ (CoherentCompletion.functor J).obj (Modules.coherentPushforwardObj f F),
      CoherentFormalMap.StagesHaveUniformKernelCokernelAnnihilation K α :=
  sorry

end AlgebraicGeometry.Scheme.CoherentFormalModules
