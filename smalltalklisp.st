Object subclass: LObj [
  LObj class >> new: t [^super new]
]

LObj subclass: Nil [
  print [^'nil']
  eval: env [^self]
]

LObj subclass: Num [
  | num |
  Num class >> new: n [^super new setData: n; yourself]
  setData: n [num := n]
  data [^num]
  print [^num printString]
  eval: env [^self]
]

LObj subclass: Sym [
  | name |
  Sym class >> new: s [^super new setData: s; yourself]
  setData: s [name := s]
  data [^name]
  print [^name]
  eval: env [
    | bind |
    bind := Util findVar: self from: env.
    (bind class) = Nil ifTrue: [
      ^Error new: name, ' has no value'
    ] ifFalse: [
      ^bind cdr
    ]
  ]
]

LObj subclass: Error [
  | msg |
  Error class >> new: s [^super new setData: s; yourself]
  setData: s [msg := s]
  data [^msg]
  print [^'<error: ', msg, '>']
  eval: env [^self]
]

LObj subclass: Cons [
  | ar dr |
  Cons class >> new: a with: d [^super new setData: a with: d; yourself]
  setData: a with: d [ar := a. dr := d]
  setCar: a [ar := a]
  setCdr: d [dr := d]
  car [^ar]
  cdr [^dr]
  print [
    | obj ret first |
    obj := self.
    ret := ''.
    first := true.
    [(obj class) = Cons] whileTrue: [
      first = true ifTrue: [
        first := false
      ] ifFalse: [
        ret := ret, ' '
      ].
      ret := ret, ((obj car) print).
      obj := obj cdr
    ].
    (obj class) = Nil ifTrue: [
      ^'(', ret, ')'
    ] ifFalse: [
      ^'(', ret, ' . ', (obj print), ')'
    ]
  ]
  eval: env [^Util evalCompound: self env: env]
]

LObj subclass: Subr [
  print [^'<subr>']
  call: args [^Error new: 'no subr implementation']
]

Subr subclass: SubrCar [
  call: args [^Util safeCar: (Util safeCar: args)]
]

Subr subclass: SubrCdr [
  call: args [^Util safeCdr: (Util safeCar: args)]
]

Subr subclass: SubrCons [
  call: args [
    ^Cons new: (Util safeCar: args) with: (Util safeCar: (Util safeCdr: args))
  ]
]

Subr subclass: SubrEq [
  call: args [
    | x y |
    x := Util safeCar: args.
    y := Util safeCar: (Util safeCdr: args).
    ((x class) = Num & (y class) = Num) ifTrue: [
      (x data) = (y data) ifTrue: [
        ^Util getT
      ] ifFalse: [
        ^Util getNil
      ]
    ] ifFalse: [
      x == y ifTrue: [
        ^Util getT
      ] ifFalse: [
        ^Util getNil
      ]
    ]
  ]
]

Subr subclass: SubrAtom [
  call: args [
    (Util safeCar: args) class = Cons ifTrue: [
      ^Util getNil
    ] ifFalse: [
      ^Util getT
    ]
  ]
]

Subr subclass: SubrNumberp [
  call: args [
    (Util safeCar: args) class = Num ifTrue: [
      ^Util getT
    ] ifFalse: [
      ^Util getNil
    ]
  ]
]

Subr subclass: SubrSymbolp [
  call: args [
    (Util safeCar: args) class = Sym ifTrue: [
      ^Util getT
    ] ifFalse: [
      ^Util getNil
    ]
  ]
]

Subr subclass: SubrAddOrMul [
  | initVal |
  SubrAddOrMul class >> new: v [^super new set: v; yourself]
  set: v [
    initVal := v.
  ]
  call: args [
    | ret a add |
    ret := initVal.
    ret = 0 ifTrue: [
      add := true
    ] ifFalse: [
      add := false
    ].
    a := args.
    [(a class) = Cons] whileTrue: [
      ((a car) class) ~= Num ifTrue: [^Error new: 'wrong type'].
      add ifTrue: [
        ret := ret + ((a car) data)
      ] ifFalse: [
        ret := ret * ((a car) data)
      ].
      a := a cdr
    ].
    ^Num new: ret
  ]
]

Subr subclass: SubrSubOrDivOrMod [
  | type |
  SubrSubOrDivOrMod class >> new: t [^super new set: t; yourself]
  set: t [
    type := t.
  ]
  call: args [
    | x y |
    x := Util safeCar: args.
    y := Util safeCar: (Util safeCdr: args).
    ((x class) ~= Num) | ((y class) ~= Num) ifTrue: [^Error new: 'wrong type'].
    type = #sub ifTrue: [^Num new: ((x data) - (y data))].
    type = #div ifTrue: [^Num new: ((x data) // (y data))].
    type = #mod ifTrue: [^Num new: ((x data) \\ (y data))]
  ]
]

LObj subclass: Expr [
  | args body env |
  Expr class >> new: a env: e [^super new setData: a env: e; yourself]
  setData: a env: e [
    args := Util safeCar: a.
    body := Util safeCdr: a.
    env := e
  ]
  print [^'<expr>']
  call: a [
    | b e ret |
    ret := Util getNil.
    b := body.
    e := Cons new: (Util pairlis: args with: a) with: env.
    [(b class) = Cons] whileTrue: [
      ret := (b car) eval: e.
      b := b cdr.
    ].
    ^ret
  ]
]

Object subclass: Util [
  kLPar :=  $(.
  kRPar :=  $).
  kQuote :=  $'.

  kNil := Nil new.
  symT := nil.
  symQuote := nil.
  symIf := nil.
  symLambda := nil.
  symDefun := nil.
  symSetq := nil.
  gEnv := nil.

  Util class >> init [
    symT := self makeSym: 't'.
    symQuote := self makeSym: 'quote'.
    symIf := self makeSym: 'if'.
    symLambda := self makeSym: 'lambda'.
    symDefun := self makeSym: 'defun'.
    symSetq := self makeSym: 'setq'.
    gEnv := Cons new: kNil with: kNil.
    self addToEnv: symT val: symT to: gEnv.

    self addToEnv: (self makeSym: 'car') val: (SubrCar new) to: gEnv.
    self addToEnv: (self makeSym: 'cdr') val: (SubrCdr new) to: gEnv.
    self addToEnv: (self makeSym: 'cons') val: (SubrCons new) to: gEnv.
    self addToEnv: (self makeSym: 'eq') val: (SubrEq new) to: gEnv.
    self addToEnv: (self makeSym: 'atom') val: (SubrAtom new) to: gEnv.
    self addToEnv: (self makeSym: 'numberp') val: (SubrNumberp new) to: gEnv.
    self addToEnv: (self makeSym: 'symbolp') val: (SubrSymbolp new) to: gEnv.
    self addToEnv: (self makeSym: '+') val: (SubrAddOrMul new: 0) to: gEnv.
    self addToEnv: (self makeSym: '*') val: (SubrAddOrMul new: 1) to: gEnv.
    self addToEnv: (self makeSym: '-')
        val: (SubrSubOrDivOrMod new: #sub) to: gEnv.
    self addToEnv: (self makeSym: '/')
        val: (SubrSubOrDivOrMod new: #div) to: gEnv.
    self addToEnv: (self makeSym: 'mod')
        val: (SubrSubOrDivOrMod new: #mod) to: gEnv.
  ]

  Util class >> getNil [^kNil]
  Util class >> getT [^symT]

  symTable := Dictionary new.
  Util class >> makeSym: s [
    ^symTable at: s ifAbsent: [
      | sym |
      sym := Sym new: s.
      symTable at: s put: sym.
      ^sym
    ]
  ]

  Util class >> match: val with: clause default: def [
    ^((Dictionary from: clause) at: val ifAbsent: [def]) value
  ]

  Util class >> safeCar: obj [
    (obj class) = Cons ifTrue: [
      ^obj car
    ] ifFalse: [
      ^kNil
    ]
  ]

  Util class >> safeCdr: obj [
    (obj class) = Cons ifTrue: [
      ^obj cdr
    ] ifFalse: [
      ^kNil
    ]
  ]

  Util class >> nreverse: lst [
    | l tmp ret |
    l := lst.
    ret := kNil.
    [(l class) = Cons] whileTrue: [
      tmp := l cdr.
      l setCdr: ret.
      ret := l.
      l := tmp
    ].
    ^ret
  ]

  Util class >> pairlis: lst1 with: lst2 [
    | l1 l2 ret |
    l1 := lst1.
    l2 := lst2.
    ret := kNil.
    [((l1 class) = Cons) & ((l2 class) = Cons)] whileTrue: [
      ret := Cons new: (Cons new: (l1 car) with: (l2 car)) with: ret.
      l1 := l1 cdr.
      l2 := l2 cdr
    ].
    ^self nreverse: ret
  ]

  Util class >> isSpace: c [
    ^ (c = $<9>) | (c = $<10>) | (c = $<13>) | (c = $<32>)
  ]

  Util class >> isDelimiter: c [
    ^ (c = kLPar) | (c = kRPar) | (c = kQuote) | (self isSpace: c)
  ]

  Util class >> skipSpaces: s [
    | i done |
    i := 1.
    done := false.
    [(i <= s size) & (done not)] whileTrue: [
      (self isSpace: (s at: i)) ifTrue: [
        i := i + 1
      ] ifFalse: [
        done := true
      ]
    ].
    ^s copyFrom: i to: s size
  ]

  Util class >> makeNumOrSym: s [
    | num |
    num := s asInteger.
    (num printString) = s ifTrue: [
      ^Num new: num
    ] ifFalse: [
      ^self makeSym: s
    ]
  ]

  Util class >> readAtom: str [
    | s i done next |
    s := str.
    next := ''.
    i := 1.
    done := false.
    [(i <= s size) & (done not)] whileTrue: [
      (self isDelimiter: (s at: i)) ifTrue: [
        next := s copyFrom: i to: s size.
        s := (s copyFrom: 1 to: (i - 1)).
        done := true
      ] ifFalse: [
        i := i + 1
      ]
    ].
    ^{self makeNumOrSym: s. next}
  ]

  Util class >> read: str [
    | s tmp |
    s := self skipSpaces: str.
    (s size) = 0 ifTrue: [
      ^{Error new: 'empty input'. ''}
    ] ifFalse: [
      self match: (s at: 1) with: {
        kRPar -> [^{Error new: 'invalid syntax: ', s. ''}].
        kLPar -> [^self readList: (s copyFrom: 2 to: s size)].
        kQuote -> [
          tmp := self read: (s copyFrom: 2 to: s size).
          ^{Cons new: symQuote with: (Cons new: (tmp at: 1) with: kNil).
            tmp at: 2}
        ]
      } default: [^self readAtom: s]
    ]
  ]

  Util class >> readList: str [
    | s ret tmp |
    s := str.
    ret := kNil.
    [
      s := self skipSpaces: s.
      (s size) = 0 ifTrue: [
        ^{Error new: 'unfinished parenthesis'. ''}
      ] ifFalse: [
        (s at: 1) = kRPar ifTrue: [
          ^{self nreverse: ret. s copyFrom: 2 to: s size}
        ] ifFalse: [
          tmp := self read: s.
          ((tmp at: 1) class) = Error ifTrue: [
            ^tmp
          ] ifFalse: [
            ret := Cons new: (tmp at: 1) with: ret.
            s := tmp at: 2
          ]
        ]
      ]
    ] repeat
  ]

  Util class >> findVar: sym from: e [
    | env alist |
    env := e.
    [(env class) = Cons] whileTrue: [
      alist := env car.
      [(alist class) = Cons] whileTrue: [
        (alist car) car == sym ifTrue: [
          ^alist car
        ] ifFalse: [
          alist := alist cdr
        ]
      ].
      env := env cdr
    ].
    ^kNil
  ]

  Util class >> addToEnv: sym val: val to: env [
    env setCar: (Cons new: (Cons new: sym with: val) with: (env car))
  ]

  Util class >> eval: obj [^obj eval: gEnv]

  Util class >> evalCompound: obj env: env [
    | op args c expr sym val bind |
    op := self safeCar: obj.
    args := self safeCdr: obj.
    op == symQuote ifTrue: [
      ^self safeCar: args
    ].
    op == symIf ifTrue: [
      c := (self safeCar: args) eval: env.
      (c class) = Error ifTrue: [
        ^c
      ] ifFalse: [
        c == kNil ifTrue: [
          ^(self safeCar: (self safeCdr: (self safeCdr: args))) eval: env
        ] ifFalse: [
          ^(self safeCar: (self safeCdr: args)) eval: env
        ]
      ]
    ].
    op == symLambda ifTrue: [
      ^Expr new: args env: env
    ].
    op == symDefun ifTrue: [
      expr := Expr new: (self safeCdr: args) env: env.
      sym := self safeCar: args.
      self addToEnv: sym val: expr to: gEnv.
      ^sym
    ].
    op == symSetq ifTrue: [
      val := (self safeCar: (self safeCdr: args)) eval: env.
      (val class) = Error ifTrue: [^val].
      sym := self safeCar: args.
      bind := self findVar: sym from: env.
      bind == kNil ifTrue: [
        self addToEnv: sym val: val to: gEnv
      ] ifFalse: [
        bind setCdr: val
      ].
      ^val
    ].
    ^self apply: (op eval: env) args: (self evlis: args env: env)
  ]

  Util class >> evlis: lst env: env [
    | l ret elm |
    l := lst.
    ret := kNil.
    [(l class) = Cons] whileTrue: [
      elm := (l car) eval: env.
      (elm class) = Error ifTrue: [
        ^elm
      ] ifFalse: [
        ret := Cons new: elm with: ret.
        l := l cdr
      ]
    ].
    ^self nreverse: ret
  ]

  Util class >> apply: fn args: args [
    (fn class) = Error ifTrue: [^fn].
    (args class) = Error ifTrue: [^args].
    (fn class superclass) = Subr ifTrue: [^fn call: args].
    (fn class) = Expr ifTrue: [^fn call: args].
    ^Error new: (fn print), ' is not function'
  ]
]

Object subclass: Lisp [
  Lisp class >> repl [
    | line |
    '> ' display.
    line := stdin nextLine.
    [line ~= nil] whileTrue: [
      (Util eval: ((Util read: line) at: 1)) print displayNl.
      '> ' display.
      line := stdin nextLine.
    ]
  ]
]

Util init.
Lisp repl.
