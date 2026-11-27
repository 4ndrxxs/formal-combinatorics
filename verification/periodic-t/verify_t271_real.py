"""Check an order-271 periodic T-system and four full circulants for real order 246068.
Usage: python verify_t271_real.py          (no nonstandard package or input file)
"""
from math import gcd
from hashlib import sha256

PERIOD = 271
SYMBOLS = (1, 2, 5, 0, 7, 0, 4, 7, 4, 0, 4, 1, 5, 4, 4, 4, 0, 0)
SECOND_SYMBOLS = (5, 4, 6, 7, 3, 1, 0, 6, 4, 6, 7, 3, 2, 2, 0, 4, 4, 0)
BLOCK_SIZE = 227
BLOCKS = (
    (43727896635352047844436095622873948551787259124413180809051433218150, 4093547649666833128273725037637111788768764818049211907069901765944, 91456254729535281352990804958087323979807009113867117325969042641073, 206767612394784178470759484869186701964634464036794994006858371819694),
    (167243266601519128864343286205848353061042997057458773859681213893055, 171951676701853070512900025073283096837309896255911399039777448775576, 7314335052865519552858410035277027379417176455634535034680197119125, 88306156772058289358934625936078331357613625078281356801294229429011),
    (193717010015006397516797659791692032003724172819540700242189006183826, 146176396516940160344219894929263101195388187767702412754601438418398, 43727896635352047844436095622873948551787259124413180809051433218150, 156773600669317997977583772454336493293885407638728160652339862197282),
    (18379148354491507334133000432707830752252491199980541260937425818273, 92913875375742653706999931087404268093535883680796363452594983397842, 100821301222364244858545786706730791794124832480041847246576959991621, 171951676701853070512900025073283096837309896255911399039777448775576),
)

def t_word(symbols):
    word = [-1] * PERIOD
    word[0] = 0
    for e in range(PERIOD-1):
        x = pow(6, e, PERIOD)
        assert word[x] == -1
        v = symbols[e % 18]
        sign, color = divmod(v, 4)
        if color:
            color = 1 + (color-1 + e//18) % 3
        word[x] = 4*sign + color
    return word

def t_correlations(word):
    return [sum((1 if (x<4)==(y<4) else -1) for j,x in enumerate(word)
                for y in [word[(j+s)%len(word)]] if x%4==y%4)
            for s in range(len(word))]

def circular_dot(a,b,s,n):
    mask = (1<<n)-1
    b = ((b | b<<n)>>s)&mask
    return n-2*(a^b).bit_count()

def main():
    w = t_word(SYMBOLS)
    assert t_correlations(w) == [271]+[0]*270
    wrong = w.copy()
    wrong[1] ^= 4
    assert any(t_correlations(wrong)[1:])
    print('T(271): four signed, disjoint coordinates; every one of the 270 off-zero shifts has sum zero.')
    second = t_word(SECOND_SYMBOLS)
    assert t_correlations(second) == [271]+[0]*270
    assert [sum(x%4==i for x in w) for i in range(4)] == [166,35,35,35]
    assert [sum(x%4==i for x in second) for i in range(4)] == [106,55,55,55]
    print('Second T(271): all shifts checked; support sizes (106,55,55,55) versus (166,35,35,35).')
    for i in range(4):
        for k in range(4):
            for v in range(BLOCK_SIZE):
                got=sum(circular_dot(BLOCKS[i][c],BLOCKS[k][c],v,BLOCK_SIZE) for c in range(4))
                assert got == (4*BLOCK_SIZE if i==k and v==0 else 0)
    print('Order 908: all 16 block-row pairs and 227 shifts checked over the integers.')
    assert gcd(PERIOD,BLOCK_SIZE)==1
    r=PERIOD*BLOCK_SIZE
    words=[]
    for c in range(4):
        letters=bytearray((r+7)//8)
        for x in range(r):
            sign,axis=divmod(w[x%PERIOD],4)
            bit=sign ^ ((BLOCKS[axis][c]>>(x%BLOCK_SIZE))&1)
            letters[x//8]|=bit<<(x%8)
        words.append(int.from_bytes(letters,'little'))
    # The entire complementary quadruple is checked directly as 61,517-bit integers.
    for s in range(r):
        assert sum(circular_dot(a,a,s,r) for a in words)==(4*r if s==0 else 0)
    payload=b''.join(a.to_bytes((r+7)//8,'little') for a in words)
    print(f'Order {4*r}: four sign sequences of length {r}; every one of {r-1} nonzero cyclic correlations sums to zero.')
    print('First-row SHA256 (four little-endian packed minus-bit words):',sha256(payload).hexdigest())
    print('Goethals-Seidel supplies the ordinary integer Hadamard matrix.')
if __name__=='__main__':
    main()

