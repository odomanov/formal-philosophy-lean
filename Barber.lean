variable
  (men : Type)
  (barber : men)
  (shaves : men → men → Prop)

theorem t1 (h : ∀ x : men, shaves barber x ↔ ¬ shaves x x) : False :=
  have ⟨bx, xx⟩ := h barber
  let sbb := shaves barber barber
  have np : sbb → False := λ x => (bx x) (xx (bx x))
  have p : sbb := xx np
  np p

theorem t2 : (∀ x : men, shaves barber x ↔ ¬ shaves x x) → False := by
  intro h
  have p := h barber
  by_cases sbb : shaves barber barber
  · have nsbb : ¬ (shaves barber barber) := p.mp sbb
    contradiction
  · have nsbb : shaves barber barber := p.mpr sbb
    contradiction
