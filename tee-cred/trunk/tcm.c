/*
 * @XMHF_LICENSE_HEADER_START@
 *
 * eXtensible, Modular Hypervisor Framework (XMHF)
 * Copyright (c) 2009-2012 Carnegie Mellon University
 * Copyright (c) 2010-2012 VDG Inc.
 * All Rights Reserved.
 *
 * Developed by: XMHF Team
 *               Carnegie Mellon University / CyLab
 *               VDG Inc.
 *               http://xmhf.org
 *
 * This file is part of the EMHF historical reference
 * codebase, and is released under the terms of the
 * GNU General Public License (GPL) version 2.
 * Please see the LICENSE file for details.
 *
 * THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND
 * CONTRIBUTORS "AS IS" AND ANY EXPRESS OR IMPLIED WARRANTIES,
 * INCLUDING, BUT NOT LIMITED TO, THE IMPLIED WARRANTIES OF
 * MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE ARE
 * DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT HOLDER OR CONTRIBUTORS
 * BE LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL,
 * EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT LIMITED
 * TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF USE,
 * DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON
 * ANY THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR
 * TORT (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF
 * THE USE OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF
 * SUCH DAMAGE.
 *
 * @XMHF_LICENSE_HEADER_END@
 */

#include <malloc.h>
#include <string.h>
#include <stdio.h>
#include <sys/stat.h>

#include "dbg.h"
#include "tcm.h"
#include "audited-kv.h"
#include "audited-kv-pal.h"
#include "audit.h"

#include <tee-sdk/tv.h>

tcm_err_t tcm_ctx_init(tcm_ctx_t* tcm_ctx,
                       audit_ctx_t* audit_ctx,
                       akv_ctx_t* akv_ctx)
{
  if (!tcm_ctx || !audit_ctx || !akv_ctx) {
    return TCM_EINVAL;
  }
  tcm_ctx->audit_ctx = audit_ctx;
  tcm_ctx->akv_ctx = akv_ctx;

  return 0;
}

void tcm_ctx_release(tcm_ctx_t* tcm_ctx)
{
}

tcm_err_t tcm_db_add(tcm_ctx_t* tcm_ctx,
                     const char* key,
                     const char* val)
{
  akv_cmd_ctx_t akv_cmd_ctx;
  bool cmd_initd=false;
  akv_err_t akv_err;
  audit_err_t audit_err;
  uint8_t audit_token[AUDIT_TOKEN_MAX];
  size_t audit_token_len = sizeof(audit_token);
  int rv = 0;

  if (!tcm_ctx || !key || !val)
    return TCM_EINVAL;

  akv_err = akv_db_add_begin(tcm_ctx->akv_ctx,
                             &akv_cmd_ctx,
                             key,
                             val,
                             strlen(val)+1);
  CHECK_RV(akv_err, TCM_EAKV | (akv_err << 8),
           "akv_db_add_begin");
  cmd_initd=true;

  audit_err = audit_get_token(tcm_ctx->audit_ctx,
                              akv_cmd_ctx.audited->audit_nonce.data,
                              akv_cmd_ctx.audited->audit_nonce.len,
                              akv_cmd_ctx.audited->audit_string,
                              strlen(akv_cmd_ctx.audited->audit_string),
                              audit_token,
                              &audit_token_len);
  CHECK_RV(audit_err, TCM_EAUDIT | (audit_err << 8),
           "audit_get_token");

  akv_err = akv_db_add_execute(&akv_cmd_ctx,
                               audit_token,
                               audit_token_len);
  CHECK_RV(akv_err, TCM_EAKV | (akv_err << 8),
           "akv_db_add_execute");

 out:
  if(cmd_initd) {
    akv_cmd_ctx_release(&akv_cmd_ctx);
  }
  return rv;
}

tcm_err_t tcm_db_get(tcm_ctx_t* tcm_ctx,
                     const char* key,
                     char** val)
{
  akv_cmd_ctx_t akv_cmd_ctx;
  bool cmd_initd=false;
  akv_err_t akv_err;
  audit_err_t audit_err;
  uint8_t audit_token[AUDIT_TOKEN_MAX];
  size_t audit_token_len = sizeof(audit_token);
  int rv = 0;
  size_t val_len;

  if (!tcm_ctx || !key || !val)
    return TCM_EINVAL;

  akv_err = akv_db_get_begin(tcm_ctx->akv_ctx,
                             &akv_cmd_ctx,
                             key);
  CHECK_RV(akv_err, TCM_EAKV | (akv_err << 8),
           "akv_db_get_begin");
  cmd_initd=true;

  audit_err = audit_get_token(tcm_ctx->audit_ctx,
                              akv_cmd_ctx.audited->audit_nonce.data,
                              akv_cmd_ctx.audited->audit_nonce.len,
                              akv_cmd_ctx.audited->audit_string,
                              strlen(akv_cmd_ctx.audited->audit_string),
                              audit_token,
                              &audit_token_len);
  CHECK_RV(audit_err, TCM_EAUDIT | (audit_err << 8),
           "audit_get_token");

  akv_err = akv_db_get_execute(&akv_cmd_ctx,
                               audit_token,
                               audit_token_len,
                               (void**)val,
                               &val_len);
  CHECK_RV(akv_err, TCM_EAKV | (akv_err << 8),
           "akv_db_get_execute");

 out:
  if(cmd_initd) {
    akv_cmd_ctx_release(&akv_cmd_ctx);
  }
  return rv;
}

void* read_file(const char *path, size_t *len)
{
  struct stat s;
  size_t toread;
  size_t numread=0;
  FILE *f=NULL;
  char *rv=NULL;
  int err;

  err=stat(path, &s);
  CHECK(!err, NULL, "stat(%s)", path);

  toread = s.st_size;

  rv = malloc(toread+1);
  CHECK_MEM(rv, NULL);

  f = fopen(path, "rb");
  CHECK(f, NULL, "fopen(%s)", path);

  while(toread > 0) {
    size_t cnt = fread(&rv[numread], 1, toread, f);
    CHECK(cnt, rv, "fread");
    toread -= cnt;
    numread += cnt;
  }
  rv[numread] = '\0';

  if(len) {
    *len=numread;
  }

 out:
  if(f) {
    err=fclose(f);
    f=NULL;
    CHECK(!err, rv, "fclose"); /* caution: potential backwards
                                  goto. ew. also, we don't change rv,
                                  since if we already successfully
                                  read the data, failing fclose
                                  doesn't matter*/
  }
  if(toread > 0) {
    free(rv);
    rv=NULL;
  }
  return rv;
}

int write_file(const char *path, uint8_t *data, size_t towrite)
{
  FILE *f=NULL;
  size_t numwritten=0;
  int rv;

  f = fopen(path, "wb");
  CHECK(f, 1, "fopen(%s)", path);

  while(towrite > 0) {
    size_t cnt = fwrite(&data[numwritten], 1, towrite, f);
    CHECK(cnt, 1, "fwrite");
    towrite -= cnt;
    numwritten += cnt;
  }

  fflush(f);

 out:
  if(f) {
    rv = fclose(f);
    f=NULL;
    CHECK(!rv, rv, "fclose"); /* caution: potential backwards goto*/
  }
  return rv;
}

int main_old(int argc, char **argv)
{
  int rv=0;
  audit_err_t audit_err;
  akv_err_t akv_err;
  tcm_err_t tcm_err;
  
  tcm_ctx_t tcm_ctx;
  audit_ctx_t audit_ctx;
  akv_ctx_t akv_ctx;
  const char* server = argv[1];
  const char* port = argv[2];
  const char* pem_pub_key_file = argv[3];
  char *pem_pub_key;

  pem_pub_key = read_file(pem_pub_key_file, NULL);
  CHECK(pem_pub_key, 1,
        "read_file %s", pem_pub_key_file);

  audit_err = audit_ctx_init(&audit_ctx, server, port);
  if (audit_err) {
    rv = 1;
    printf("audit_ctx_init failed with rv 0x%x\n", audit_err);
    goto cleanup_none;
  }

  akv_err = akv_ctx_init(&akv_ctx, pem_pub_key);
  if (akv_err) {
    rv = 2;
    printf("akv_ctx_init failed with rv 0x%x\n", akv_err);
    goto cleanup_audit;
  }

  tcm_err = tcm_ctx_init(&tcm_ctx, &audit_ctx, &akv_ctx);
  if (tcm_err) {
    rv = 3;
    printf("tcm_ctx_init failed with rv 0x%x\n", tcm_err);
    goto cleanup_akv;
  }

  tcm_err = tcm_db_add(&tcm_ctx,
                       "key",
                       "val");
  if (tcm_err) {
    rv = 4;
    printf("tcm_db_add failed with 0x%x\n", tcm_err);
    goto cleanup_tcm;
  }

  {
    akv_err_t akv_err;
    uint8_t *data;
    size_t len;
    akv_err = akv_export(tcm_ctx.akv_ctx,
                         &data,
                         &len);
    if (akv_err) {
      rv=5;
      printf("akv_export failed with 0x%x\n", akv_err);
      goto cleanup_tcm;
    }
    write_file("db", data, len);
  }

  {
    akv_err_t akv_err;
    uint8_t *data;
    size_t len;

    data = read_file("db", &len);
    akv_err = akv_import(tcm_ctx.akv_ctx,
                         data,
                         len);
    if (akv_err) {
      rv=6;
      printf("akv_import failed with 0x%x\n", akv_err);
      goto cleanup_tcm;
    }
  }

  {
    char *val;
    tcm_err = tcm_db_get(&tcm_ctx,
                         "key",
                         &val);
    if (tcm_err) {
      rv = 4;
      printf("tcm_db_get failed with 0x%x\n", tcm_err);
      goto cleanup_tcm;
    }
    printf("retrieved val:%s\n", val);
    free(val);
    val=NULL;
  }

 cleanup_tcm:
  tcm_ctx_release(&tcm_ctx);
 cleanup_akv:
  akv_ctx_release(&akv_ctx);
 cleanup_audit:
  audit_ctx_release(&audit_ctx);
 out:
 cleanup_none:
  return rv;
} 

#include <gtk/gtk.h>

int tcm_gtk_main (int argc, char **argv, tcm_ctx_t *tcm_ctx);
int main (int argc, char **argv)
{
  int rv=0;
  audit_err_t audit_err;
  akv_err_t akv_err;
  tcm_err_t tcm_err;
  
  tcm_ctx_t tcm_ctx;
  audit_ctx_t audit_ctx;
  akv_ctx_t akv_ctx;
  const char* server = argv[1];
  const char* port = argv[2];
  const char* pem_pub_key_file = argv[3];
  char *pem_pub_key;

  pem_pub_key = read_file(pem_pub_key_file, NULL);
  CHECK(pem_pub_key, 1,
        "read_file %s", pem_pub_key_file);

  audit_err = audit_ctx_init(&audit_ctx, server, port);
  CHECK_RV(audit_err, audit_err, "audit_ctx_init");

  akv_err = akv_ctx_init(&akv_ctx, pem_pub_key);
  CHECK_RV(akv_err, akv_err, "akv_ctx_init");

  tcm_err = tcm_ctx_init(&tcm_ctx, &audit_ctx, &akv_ctx);
  CHECK_RV(tcm_err, tcm_err, "tcm_ctx_init");

  if (g_file_test("db", G_FILE_TEST_IS_REGULAR)) {
    /* import */
    akv_err_t akv_err;
    uint8_t *data;
    size_t len;

    data = read_file("db", &len);
    akv_err = akv_import(tcm_ctx.akv_ctx,
                         data,
                         len);
    if (akv_err) {
      rv=6;
      printf("akv_import failed with 0x%x\n", akv_err);
      goto out;
    }
  }

  tcm_gtk_main(argc, argv, &tcm_ctx);

  /* XXX export */

 out:
  /* FIXME cleanup */
  return rv;
}

typedef struct {
  GtkBox *box;
  GList *keys;
} box_and_labels_t;

/* consumes key and value */
static void insert_sorted( box_and_labels_t *bl,
                           gchar *key,
                           gchar *value)
{
  GtkWidget *expander;
  GtkWidget *label;
  int pos;

  expander = gtk_expander_new (key);

  /* get sorted position */
  bl->keys = g_list_insert_sorted(bl->keys,
                                  key,
                                  (GCompareFunc)g_strcmp0);
  pos = g_list_index(bl->keys, key);
  assert(pos >= 0);

  /* create and insert expander */
  gtk_box_pack_start (bl->box,
                      expander,
                      FALSE, FALSE, 0);
  gtk_box_reorder_child (bl->box,
                         expander,
                         pos);

  /* add expander contents */
  label = gtk_label_new (value);
  gtk_label_set_selectable (GTK_LABEL(label), TRUE);
  gtk_container_add (GTK_CONTAINER (expander), label);


  gtk_widget_show_all(expander);
}

static void add_button_handler(box_and_labels_t *bl)
{
  GtkWidget *dialog;
  GtkWidget *table;
  GtkWidget *keyEntry, *valEntry;

  dialog = gtk_dialog_new_with_buttons("Add a secret", NULL,
                                       GTK_DIALOG_MODAL,
                                       GTK_STOCK_ADD, GTK_RESPONSE_OK,
                                       GTK_STOCK_CANCEL, GTK_RESPONSE_CANCEL,
                                       NULL);
  table = gtk_table_new(2, 2, FALSE);
  gtk_box_pack_start_defaults (GTK_BOX (GTK_DIALOG (dialog)->vbox), table);
  
  gtk_table_attach(GTK_TABLE(table),
                   gtk_label_new("Key"),
                   0, 1, 0, 1,
                   GTK_SHRINK | GTK_FILL,
                   GTK_SHRINK | GTK_FILL,
                   0, 0);
  keyEntry = gtk_entry_new();
  gtk_table_attach(GTK_TABLE(table),
                   keyEntry,
                   1, 2, 0, 1,
                   GTK_SHRINK | GTK_FILL,
                   GTK_SHRINK | GTK_FILL,
                   0, 0);

  gtk_table_attach(GTK_TABLE(table),
                   gtk_label_new("Value"),
                   0, 1, 1, 2,
                   GTK_SHRINK | GTK_FILL,
                   GTK_SHRINK | GTK_FILL,
                   0, 0);
  valEntry = gtk_entry_new();
  gtk_table_attach(GTK_TABLE(table),
                   valEntry,
                   1, 2, 1, 2,
                   GTK_SHRINK | GTK_FILL,
                   GTK_SHRINK | GTK_FILL,
                   0, 0);

  gtk_widget_show_all(dialog);

  if(gtk_dialog_run (GTK_DIALOG (dialog)) == GTK_RESPONSE_OK) {
    const gchar *key, *val;
    key = gtk_entry_get_text(GTK_ENTRY(keyEntry));
    val = gtk_entry_get_text(GTK_ENTRY(valEntry));

    if(!key || !strlen(key)
       || !val || !strlen(val)) {
      g_warning("NULL key or val");
      goto out;
    }

    insert_sorted(bl, g_strdup(key), g_strdup(val));
  }

 out:
  gtk_widget_destroy(dialog);
}

int tcm_gtk_main (int argc, char **argv, tcm_ctx_t *tcm_ctx)
{
  GtkWidget *window;
  GtkWidget *button;
  GtkWidget *vbox;
  int rv=0;
  box_and_labels_t box_and_labels;

  gtk_init (&argc, &argv);

  { /* window */
    window = gtk_window_new (GTK_WINDOW_TOPLEVEL);
    gtk_window_set_title (GTK_WINDOW (window), "TEE-Cred");
    g_signal_connect (window, "destroy",
                      G_CALLBACK (gtk_main_quit), NULL);
    g_signal_connect (window, "delete-event",
                      G_CALLBACK (gtk_main_quit), NULL);
    gtk_container_set_border_width (GTK_CONTAINER (window), 10);
  }

  { /* vbox */
    vbox = gtk_vbox_new (TRUE, 5);
    gtk_box_set_homogeneous (GTK_BOX(vbox), FALSE);
    gtk_container_add (GTK_CONTAINER (window), vbox);
  }
  box_and_labels = (box_and_labels_t) {
    .box = GTK_BOX(vbox),
    .keys = NULL,
  };

  /* /\* expanders *\/ */
  /* for(i=0; i< sizeof(keys)/sizeof(keys[0]); i++) {  */
  /*   GtkWidget *expander; */
  /*   GtkWidget *label; */
  /*   expander = gtk_expander_new (keys[i]); */
  /*   gtk_box_pack_start (GTK_BOX (vbox), */
  /*                       expander, */
  /*                       FALSE, FALSE, 0); */

  /*   label = gtk_label_new ("labeeeel"); */
  /*   gtk_label_set_selectable (GTK_LABEL(label), TRUE); */
  /*   gtk_container_add (GTK_CONTAINER (expander), label); */
  /* } */

  { /* add-button */
    button = gtk_button_new_from_stock (GTK_STOCK_ADD);
    g_signal_connect_swapped (button, "clicked",
                              G_CALLBACK (add_button_handler),
                              &box_and_labels);
    gtk_box_pack_end (GTK_BOX (vbox),
                      button,
                      FALSE, FALSE, 0);
  }

  gtk_widget_show_all (window);
  gtk_main ();

  goto out;
 out:
  return rv;
}
