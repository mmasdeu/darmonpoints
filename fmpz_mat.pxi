include "sage/libs/flint/fmpz.pxi"
include "sage/libs/ntl/decl.pxi"

cdef extern from "flint/fmpz.h":
    ctypedef void* fmpz_t
    void fmpz_init_set(fmpz_t f, const fmpz_t g)
    void fmpz_init_set_ui(fmpz_t f, unsigned long g)

    void fmpz_init(fmpz_t f)
    void fmpz_set_ui(fmpz_t f, unsigned long val)
    void fmpz_set_mpz(fmpz_t f, const mpz_t val)
    void fmpz_get_mpz(fmpz_t f, const mpz_t val)
    void fmpz_fdiv_r( fmpz_t f , const fmpz_t g , const fmpz_t h )
    int fmpz_print( fmpz_t x)

cdef extern from "flint/fmpz_mat.h":
    ctypedef void* fmpz_mat_t

    void fmpz_mat_init(fmpz_mat_t mat,unsigned long rows,unsigned long cols)
    int fmpz_mat_print_pretty( const fmpz_mat_t mat )
    fmpz_t fmpz_mat_entry(fmpz_mat_t mat ,long i ,long j)
    void fmpz_mat_zero( fmpz_mat_t mat )
    void fmpz_mat_one( fmpz_mat_t mat )
    void fmpz_mat_scalar_mul_si( fmpz_mat_t B , const fmpz_mat_t A , long c )

    void fmpz_mat_mul( fmpz_mat_t C , const fmpz_mat_t A , const  fmpz_mat_t B )
    void fmpz_mat_sqr( fmpz_mat_t B , const  fmpz_mat_t A )
    void fmpz_mat_add( fmpz_mat_t C , const fmpz_mat_t A , const  fmpz_mat_t B )
    void fmpz_mat_sub( fmpz_mat_t C , const fmpz_mat_t A , const  fmpz_mat_t B )
    void fmpz_mat_pow( fmpz_mat_t C , const fmpz_mat_t A , unsigned long n )

    void fmpz_mat_clear(fmpz_mat_t mat)

    void fmpz_mat_set(fmpz_mat_t result, fmpz_mat_t mat)
    void fmpz_mat_zero(fmpz_mat_t mat)
