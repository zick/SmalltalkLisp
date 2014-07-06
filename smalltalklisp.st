Object subclass: LObj [
  LObj class >> new: t [^super new]
]

LObj subclass: Nil [
  Nil class >> new [^super new]
]

LObj subclass: Num [
  | num |
  Num class >> new: n [^super new setData: n; yourself]
  setData: n [num := n]
  data [^num]
]

LObj subclass: Sym [
  | name |
  Sym class >> new: s [^super new setData: s; yourself]
  setData: s [name := s]
  data [^name]
]

LObj subclass: Error [
  | msg |
  Error class >> new: s [^super new setData: s; yourself]
  setData: s [msg := s]
  data [^msg]
]

LObj subclass: Cons [
  | ar dr |
  Cons class >> new: a with: d [^super new setData: a with: d; yourself]
  setData: a with: d [ar := a. dr := d]
  setCar: a [ar := a]
  setCdr: d [ar := d]
  car [^ar]
  cdr [^dr]
]

Object subclass: Util [
  kLPar :=  $(.
  kRPar :=  $).
  kQuote :=  $'.

  kNil := Nil new.

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
    self match: obj class with: {
      Cons -> [^obj car]
    } default: [^kNil]
  ]

  Util class >> safeCdr: obj [
    self match: obj class with: {
      Cons -> [^obj cdr]
    } default: [^kNil]
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
    | s |
    s := self skipSpaces: str.
    (s size) = 0 ifTrue: [
      ^{Error new: 'empty input'. ''}
    ] ifFalse: [
      self match: (s at: 1) with: {
        kRPar -> [^{Error new: 'invalid syntax: ', s. ''}].
        kLPar -> [^{Error new: 'noimpl'. ''}].
        kQuote -> [^{Error new: 'noimpl'. ''}]
      } default: [^self readAtom: s]
    ]
  ]
]

Object subclass: Lisp [
  Lisp class >> repl [
    | line |
    '> ' display.
    line := stdin nextLine.
    [line ~= nil] whileTrue: [
      (Util read: line) displayNl.
      '> ' display.
      line := stdin nextLine.
    ]
  ]
]

Lisp repl.
