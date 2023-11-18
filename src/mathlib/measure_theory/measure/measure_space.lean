import measure_theory.measure.measure_space

open measure_theory

variables {Ω : Type*} [measurable_space Ω] {μ : measure Ω}

instance ae_ne_bot.to_ne_zero [μ.ae.ne_bot] : ne_zero μ := ⟨ae_ne_bot.1 ‹_›⟩
