module

public import ReasLib.FieldTheory.Transcendence.PurelyTranscendental

@[expose] public section

universe u v

#check (RingHom.IsPurelyTranscendental :
  {F : Type u} → {E : Type v} → [Field F] → [Field E] → (F →+* E) → Prop)

#check (RingHom.isPurelyTranscendental_algebraMap_iff :
  ∀ {F : Type u} {E : Type v} [Field F] [Field E] [Algebra F E],
    (algebraMap F E).IsPurelyTranscendental ↔ FieldExtension.IsPurelyTranscendental F E)
